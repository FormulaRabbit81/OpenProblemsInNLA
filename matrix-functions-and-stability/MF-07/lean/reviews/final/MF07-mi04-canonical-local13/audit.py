"""Independent, read-only MF07 canonical package audit; no Lean execution.

Run with the existing formalization Python venv. Outputs belong only to this
new review directory. Original package and handoff are never modified.
"""
from pathlib import Path
from hashlib import sha256
import datetime, difflib, json, os, re, subprocess, sys
import yaml

R = Path(__file__).resolve().parent
B = R.parent.parent
P = B / 'MF07-canonical-package-local13'
H = B / 'MF07-canonical-local13-handoff'
F = B / 'reviews/MF07-mi04-final-local13'
I = Path('/private/tmp/nla-lean-next-mf22-worktree')
checks = []
bindings = {}

def check(ok, label):
    if not ok:
        raise AssertionError(label)
    checks.append(label)

def digest(data):
    return sha256(data).hexdigest()

def bind(path, expected=None):
    p = Path(path).resolve()
    check(p.is_file(), 'file exists: ' + str(p))
    data = p.read_bytes()
    h = digest(data)
    if expected is not None:
        check(h == expected, 'SHA256: ' + str(p))
    bindings[os.path.relpath(p, R)] = h
    return data

def js(path, expected=None):
    return json.loads(bind(path, expected))

pm = js(P/'PACKAGE-MANIFEST.json', '05631b9d2bd90565fd2aa69d86e071a6b8bad212f6f190bc0f5929025e41eeb8')
physical = {p.relative_to(P).as_posix() for p in P.rglob('*') if p.is_file()}
check(not any(p.is_symlink() for p in P.rglob('*')), 'no package symlinks')
check(len(pm['files']) == 240 and len(physical) == 241, '240 inventoried files plus manifest = 241 physical files')
check(physical == set(pm['files']) | {'PACKAGE-MANIFEST.json'}, 'closed complete package inventory')
for rel, h in pm['files'].items():
    check(not Path(rel).is_absolute() and '..' not in Path(rel).parts, 'package path stays inside: ' + rel)
    bind(P/rel, h)

hm = js(H/'MANIFEST.json', '2336cfab9a0edcf47630cb55bbd904ec5fce67f252e7e131b2e955f05196b798')
for rel, h in hm['files'].items():
    bind(H/rel, h)
bind(hm['preparer_script']['path'], hm['preparer_script']['sha256'])
bind(hm['package_manifest']['path'], hm['package_manifest']['sha256'])
hb = js(H/'BINDINGS.json')
for rel, h in hb.items():
    bind(H/rel, h)

retained = js(P/'verification/RETAINED-PATHS.json')
for x in retained:
    check(bind(x['original_path'], x['sha256']) == bind(P/x['retained_path'], x['sha256']),
          'retained exact original: ' + x['retained_path'])

fm = js(F/'MANIFEST.json', '8a90afee899c3130ede6eebb1133666288649b23567ce617135e6148f67bc687')
for rel, x in fm['files'].items():
    bind(F/rel, x['sha256'])
prior_map = js(F/'SOURCE-MAP.json')
prior = {('Solution.lean' if k == 'NLA/MF07/Complete.lean' else k): v['sha256'] for k,v in prior_map.items()}
active = js(P/'ACTIVE-SOURCE-MANIFEST.json')
impl = js(P/'IMPLEMENTATION-MAP.json')
acc = js(P/'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json', '4ce2483aa1909c5a319d87c734bf6ec9d173071b239b6a8a3f159ba46b00c919')
check(active['source_sha256'] == impl['source_sha256'] == acc['accepted_source_sha256'] == prior,
      'all21 sources equal independent full mathematical review and exact accepted local graph')
check(len(prior)==21 and active['mathematical_module_count']==20 and active['export_count']==18,
      '20 mathematical files, one wrapper, 18 exports')
for rel,h in prior.items():
    bind(P/rel,h)
    check(bind(P/rel) == bind(acc['selected_source_locations'][rel]), 'current selected source bytes: '+rel)

freeze = js(P/'STATEMENT-FREEZE.json', '6e792469355b1553d8a08d608c20c67cbfde2f067292a15e0ad119b63609037c')
check(len(freeze['frozen_files_sha256'])==10, 'ten frozen files')
for rel,h in freeze['frozen_files_sha256'].items():
    bind(P/freeze['snapshot_directory']/rel,h)
    if rel != 'lakefile.toml':
        bind(P/rel,h)
old_lake = bind(P/freeze['snapshot_directory']/'lakefile.toml').decode()
new_lake = bind(P/'lakefile.toml').decode()
expected_lake = old_lake.replace('defaultTargets = ["Challenge"]','defaultTargets = ["Solution"]') + '\n[[lean_lib]]\nname = "Solution"\n'
check(new_lake==expected_lake, 'Lake only selects and registers the Solution library')
patch = ''.join(difflib.unified_diff(old_lake.splitlines(keepends=True),new_lake.splitlines(keepends=True),fromfile='historical-draft/lakefile.toml',tofile='lakefile.toml'))
check(patch == bind(P/'verification/packaging/LAKE-DEFAULT.patch').decode(), 'exact disclosed Lake patch')
check('defaultTargets = ["Solution"]' in new_lake and set(re.findall(r'\[\[lean_lib\]\]\s+name = "([^"]+)"',new_lake))=={'NLA','Challenge','Solution'},'independent challenge and actual solution libraries present')
check('rev = "621a43d7cf21f87872392a01e874f2f1dbddc926"' in new_lake,'LeanCert Lake requirement unchanged')
check(bind(P/'lean-toolchain').decode().strip()=='leanprover/lean4:v4.33.1','exact Lean toolchain')
manifest = js(P/'lake-manifest.json')
pins = {x['name']:x['rev'] for x in manifest['packages']}
check(len(pins)==10 and pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926','ten original pinned packages')

comp = js(P/'comparator.json')
names = comp['theorem_names']
check(names==freeze['statement_names'] and len(names)==18 and len(set(names))==18,'exact frozen Comparator declarations')
check(comp['definition_names']==[] and set(comp['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'},'no definition holes or added permitted axioms')
challenge = bind(P/'Challenge.lean').decode()
solution = bind(P/'Solution.lean').decode()
check(len(re.findall(r'^\s*sorry\s*$', challenge,re.M))==18,'18 intentional Challenge holes (comment mentions excluded)')
check('import Challenge' not in solution and solution.count('#assert_trust ')==18,'complete solution excludes Challenge and checks18 kernel trusts')

def header(text, name):
    m = re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(name)+r'\b[\s\S]*?\s:=',text,re.M)
    check(m is not None,'declaration header found: '+name)
    s=m.group(0).strip()
    pos=m.start()+len(m.group(0))-len(m.group(0).lstrip())
    return s, text[:pos].count('\n')+1

check([x['declaration'] for x in impl['export_locations']]==names,'implementation index has exact ordered18 exports')
prior_headers={x['name']:x for x in js(F/'STATEMENT-COMPARISON.json')}
syntax_differences=[]
for e in impl['export_locations']:
    text=bind(P/e['path'],e['file_sha256']).decode()
    a,al=header(text,e['declaration'].split('.')[-1]);c,cl=header(challenge,e['declaration'].split('.')[-1])
    check(' '.join(a.split())==prior_headers[e['declaration']]['implementation_header'] and ' '.join(c.split())==prior_headers[e['declaration']]['frozen_header'], 'both headers identical to prior complete source review: '+e['declaration'])
    check(digest(a.encode())==e['implementation_header_sha256'] and digest(c.encode())==e['challenge_header_sha256'],'independent recorded raw header hashes: '+e['declaration'])
    if a!=c:
        syntax_differences.append(e['declaration'])
        if e['declaration']=='NLA.MF07.radius_one_semantics':
            check(' '.join(c.replace('Filter.Tendsto','Tendsto').replace('Filter.atTop','atTop').split())==' '.join(a.split()), 'only previously reviewed Filter name qualification/whitespace difference')
        elif e['declaration']=='NLA.MF07.rounded_extremal_norm':
            check(c.replace('∃ Q : Square d, ∃ σ : Fin d → ℝ, ∃ w : EuclideanVector d → ℝ,','∃ (Q : Square d) (σ : Fin d → ℝ) (w : EuclideanVector d → ℝ),')==a, 'only previously reviewed grouped existential binder syntax difference')
        else:
            check(False,'unexpected new raw header difference: '+e['declaration'])
    check(al==e['line'] and cl==e['challenge_line'],'recorded declaration lines: '+e['declaration'])
    check(acc['observed_axioms'][e['declaration']]==['propext','Classical.choice','Quot.sound'],'actual local permitted axiom list: '+e['declaration'])

pathmap=js(P/'verification/local-development/PATH-MAP.json')
for original,x in pathmap.items():
    check(bind(original,x['sha256'])==bind(P/x['path'],x['sha256']),'local runtime exact retained origin: '+x['path'])
for name,c in acc['actual_commands'].items():
    check(c['exit_code']==0,'recorded accepted command exit0: '+name)
    for field in ['receipt','log']:
        check(c[field] in pathmap,'accepted command retained '+field+': '+name)
        check(pathmap[c[field]]['sha256']==c[field+'_sha256'],'accepted command '+field+' hash: '+name)
check(len(acc['actual_commands'])==21,'all21 local command origins retained')
check(acc['canonical_verification_completed'] is False and acc['comparator_run'] is False,'local acceptance is not canonical/Comparator acceptance')

meta=yaml.safe_load(bind(P/'formalization.yaml'))
pub=js(P/'PUBLICATION-EVIDENCE.json')
idx=js(P/'reviews/INDEX.json')
check(active['whole_problem_verified'] is False and active['canonical_verification_completed'] is False and active['publication_commit'] is None and active['canonical_run_id'] is None,'active source metadata marks all canonical/publication gates pending')
check(pub['canonical_verification_completed'] is False and pub['canonical_run_id'] is None and pub['published_commit'] is None and pub['status_and_count_changed'] is False,'publication evidence invents no success/commit/run/count')
check(meta['status']['whole_problem_verified'] is False and meta['verification']['canonical_verification_completed'] is False,'formalization whole-problem/canonical flags remain false')
check(meta['review']['reviewers']==[] and 'pending' in idx['final_nonauthor_full_source_reviews'],'sealed package honestly predates final source-review attachment')
for e in idx['historical_reports']:
    bind(P/e['path'],e['sha256'])
for key in ['receipt','local_acceptance','local_receipt']:
    e=meta['verification']['statement_elaboration'] if key=='receipt' else meta['verification']
    bind(P/e[key],e.get(key+'_sha256'))
for key in ['active_source_manifest','implementation_map','local_acceptance','local_evidence_path_map','source_review_index','configuration_transition','original_source_privacy']:
    check((P/pub[key]).is_file(),'active publication evidence link: '+key)
for key,value in meta['alignment'].items():
    check((P/value).is_file(),'active formalization alignment link: '+key)

omits=js(P/'verification/OMITTED-ORIGINALS.json')
check(len(omits['privacy_omissions'])==1,'one disclosed contact-bearing original omission')
for x in omits['privacy_omissions']:
    bind(x['original_path'],x['sha256'])
    check(not (P/x['intended_path']).exists(),'omitted original not silently republished')
    check('/blob/ce47b5630bf3680d9211131c3a43825b022c139a/' in x['immutable_source'],'immutable original manuscript reference')
privacy_hits=[]
email=re.compile(rb'[A-Za-z0-9.!#$%&\x27*+/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9.-]*[A-Za-z0-9])?\.[A-Za-z]{2,}')
for rel in sorted(physical):
    if email.search((P/rel).read_bytes()) or b'mailto:' in (P/rel).read_bytes().lower():
        privacy_hits.append(rel)
check(not privacy_hits,'all241 package files contain no email-address/contact links')

readme=bind(P/'README.md').decode()
for s in ['George Stepaniants','Department of Computing and Mathematical Sciences','California Institute of Technology','Matthew J. Colbrook','Department of Applied Mathematics and Theoretical Physics','University of Cambridge','Epperlein and Wirth','OpenAI Codex','Apache 2.0']:
    check(s in readme,'attribution/license: '+s)
links=[]
for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',readme):
    if re.match(r'[A-Za-z]+://',target) or target.startswith('#'):
        continue
    dest=target.split('#',1)[0]
    if dest=='../../../tools/lean/HARNESS.md':
        bind(I/'tools/lean/HARNESS.md')
        links.append({'target':target,'resolution':'canonical repository root tools/lean/HARNESS.md'})
    else:
        check((P/dest).is_file(),'active README relative link: '+dest)
        links.append({'target':target,'resolution':dest})

validator=I/'tools/lean/validate_manifest.py'
schema=I/'docs/lean/schema/v0.4.schema.json'
bind(validator);bind(schema,'25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce')
check(bind(P/'verification/packaging/v0.4.schema.json')==bind(schema),'retained exact actual shared schema')
proc=subprocess.run([sys.executable,str(validator),str(P)],capture_output=True,text=True)
(R/'schema-validation.log').write_text(proc.stdout+proc.stderr)
check(proc.returncode==0 and 'PASS (18 declarations)' in proc.stdout,'actual unchanged shared schema/coverage validator passes18')

# Assert that this audit itself has not changed any input bytes.
for rel,h in pm['files'].items():
    check(digest((P/rel).read_bytes())==h,'package unchanged after audit: '+rel)
check(digest((P/'PACKAGE-MANIFEST.json').read_bytes())=='05631b9d2bd90565fd2aa69d86e071a6b8bad212f6f190bc0f5929025e41eeb8','package seal unchanged after audit')

out={'reviewer':'/root/mi04_independent_referee','role':'independent nonauthor MF07 package referee; prior independent complete-source review retained',
     'checks_passed':len(checks),'checks':checks,'binding_count':len(bindings),'physical_package_files':241,
     'retained_original_records':len(retained),'runtime_path_map_records':len(pathmap),'handoff_origin_bindings':len(hb),
     'exact_accepted_Lean_inputs':21,'frozen_originals':10,'frozen_exports':18,'schema_validator_exit_code':proc.returncode,
     'previously_reviewed_header_syntax_differences':syntax_differences,
     'package_approval':True,'new_Lean_execution':False,'canonical_verification':False,'Git_or_publication_action':False,'count_change':0}
(R/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
(R/'BINDINGS.json').write_text(json.dumps(dict(sorted(bindings.items())),indent=2)+'\n')
(R/'ACTIVE-LINKS.json').write_text(json.dumps(links,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))

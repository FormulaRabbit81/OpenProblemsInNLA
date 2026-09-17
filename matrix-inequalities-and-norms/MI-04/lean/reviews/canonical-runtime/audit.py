from pathlib import Path
import datetime, hashlib, json, re, subprocess, zipfile
B=Path('/tmp/nla-lean-next-20260915')
P=B/'MI04-canonical-run-35150473054'; A=P/'artifacts/lean-MI-04'; E=A/'verify-20260916T210747Z-4155'
OUT=Path(__file__).parent
REPO=Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
HEAD='63340ef17139606dce03c4d9000288129b773157'; REL='matrix-inequalities-and-norms/MI-04/lean/'
bindings={}; gitmap={}
def sha(b): return hashlib.sha256(b).hexdigest()
def read(p):
 b=Path(p).read_bytes(); bindings[str(p)]=sha(b); return b
def js(p):return json.loads(read(p))
def blob(p):
 b=subprocess.check_output(['git','-C',str(REPO),'show',HEAD+':'+REL+p]); gitmap[p]=sha(b); return b
r=js(E/'result.json'); run=js(P/'run.json'); jobs=js(P/'jobs.json'); artifacts=js(P/'artifacts.json')
identity=js(P/'FETCH-IDENTITY.json'); generic=js(P/'ROOT-AUDIT.json')
read(P/'ROOT-RAW-LOG-CORRESPONDENCE.json'); read(B/'audit_canonical_runtime.py')
assert bindings[str(B/'audit_canonical_runtime.py')]=='77bcb3744ddb210972f82784be94001c9c7be34d26b3dc7b4d539dbc07352602'
assert run['id']==35150473054 and run['head_sha']==HEAD and run['status']=='completed' and run['conclusion']=='success'
assert r['repository_commit']==HEAD and r['project']==REL.rstrip('/') and r['result']=='comparator-accepted'
assert r['semantic_review']=='not-performed-by-this-command'
inputs=r['input_sha256']
paths=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','--name-only',HEAD,'--',REL],text=True).splitlines()
assert len(inputs)==233 and {p[len(REL):] for p in paths}==set(inputs)
for p,h in inputs.items():assert sha(blob(p))==h,p
local=js(B/'MI04-LOCAL-DEVELOPMENT-ACCEPTANCE.json')
prior=B/'reviews/MI04-ie13-local-complete-development06'; prior_manifest=js(prior/'MANIFEST.json')
assert sha((prior/'MANIFEST.json').read_bytes())=='748e0fbd7af197867d1c49ecc9ab269fd39a6df5fa4e70986c3c25a8e140cc35'
for p,h in prior_manifest['files'].items():assert sha(read(prior/p))==h,p
oldbind=js(prior/'SOURCE-BINDINGS.json')
math=local['accepted_source_sha256']; assert len(math)==21
for p,h in math.items():
 assert inputs[p]==h,(p,'canonical math changed')
 oldpath=local['selected_source_locations'][p]
 # /tmp and /private/tmp are aliases; compare each reviewed path's resolved identity.
 matches=[v for k,v in oldbind.items() if Path(k).resolve()==Path(oldpath).resolve()]
 assert matches and set(matches)=={h},(p,'prior independent source binding')
solution=blob('Solution.lean').decode(); challenge=blob('Challenge.lean').decode()
assert 'import Challenge' not in solution and 'import NLA.MI04.Conclusion' in solution
freeze=json.loads(blob('STATEMENT-FREEZE.json')); frozen=freeze['frozen_files_sha256']
assert frozen==local['frozen_files_sha256'] and len(frozen)==10
for p,h in frozen.items():assert sha(blob('statement-audit/snapshots/'+p))==h,p
for p,h in frozen.items():
 if p!='lakefile.toml': assert sha(blob(p))==h,p
oldlake=blob('statement-audit/snapshots/lakefile.toml'); newlake=blob('lakefile.toml')
assert oldlake.replace(b'defaultTargets = ["Challenge"]',b'defaultTargets = ["Solution"]')==newlake
transition=json.loads(blob('verification/packaging/TRANSITION.json'))
assert transition['proof_name_transport']=='NLA/MI04/Complete.lean -> Solution.lean; exact bytes unchanged'
config=json.loads(blob('comparator.json'));assert config==r['config']
names=config['theorem_names'];assert len(names)==21 and len(set(names))==21
assert names==['NLA.MI04.'+x for x in freeze['statement_names']]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound'] and config['definition_names']==[]
assert re.findall(r'^#print axioms (\w+)',solution,re.M)==freeze['statement_names']
assert re.findall(r'^#assert_trust kernel (\w+)',solution,re.M)==freeze['statement_names']
upper=blob('NLA/MI04/UpperBound.lean').decode()
assert 'interval_decide (trust := kernel)' in upper and upper.count('quarter_gap_certificate')>=3
manifest=json.loads(blob('lake-manifest.json'))
pins={x['name']:x['rev'] for x in manifest['packages']}
assert pins==local['dependency_commits'] and len(pins)==10
raw=read(P/'job-104977317684.log').decode()
assert HEAD in raw and 'PASS: fresh Comparator run and all controls.' in raw
ansi=re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
def norm(s):return ansi.sub('',s).strip()
lines=[re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '',l) for l in raw.splitlines()]
correspondence=[]
for f in sorted(A.rglob('*.log')):
 data=read(f).decode(); rel=f.relative_to(A).as_posix()
 marks=[i for i,l in enumerate(lines) if l=='Log: /home/runner/work/_temp/nla-lean-tools/logs/'+rel]
 assert len(marks)==1,rel
 start=marks[0]+1
 end=next(k for k in range(start,len(lines)) if
   (lines[k].startswith('Running ') and k+1<len(lines) and lines[k+1].startswith('Log: ')) or
   lines[k].startswith('PASS: fresh Comparator run') or lines[k].startswith('Tools built;'))
 actual=[norm(s) for s in lines[start:end] if norm(s)]
 payload=[norm(s) for s in data.splitlines()[1:] if norm(s) and not s.startswith('EXIT_STATUS=')]
 assert actual==payload,rel
 status=re.findall(r'^EXIT_STATUS=(\d+)$',data,re.M);assert len(status)==1,rel
 assert int(status[0])==(1 if f.name in ['negative-sorry.log','negative-native.log'] else 0),rel
 correspondence.append({'path':rel,'sha256':sha(data.encode()),'payload_lines':len(payload),'actual_job_lines':[start+1,end], 'exit_code':int(status[0])})
assert len(correspondence)==12
zdata=read(P/'lean-MI-04.zip')
with zipfile.ZipFile(P/'lean-MI-04.zip') as z:
 members=z.namelist(); assert len(members)==len(set(members))==13
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in members)
 assert set(members)=={p.relative_to(A).as_posix() for p in A.rglob('*') if p.is_file()}
 for n in members:assert z.read(n)==read(A/n),n
artifact=next(x for x in artifacts['artifacts'] if x['id']==10468904090)
assert artifact['digest']=='sha256:'+sha(zdata) and artifact['workflow_run']['head_sha']==HEAD and not artifact['expired']
assert f'SHA256 digest of uploaded artifact zip is {sha(zdata)}' in raw
actualjobs={x['name']:x for x in jobs['jobs']}
verify=next(x for x in jobs['jobs'] if x['id']==104977317684)
assert verify['conclusion']=='success' and verify['head_sha']==HEAD
skip=next(x for x in jobs['jobs'] if x['id']==104977319650);assert skip['conclusion']=='skipped'
log=(E/'comparator.log').read_text()
prints=re.findall(r"info: Solution\.lean:\d+:0: '(NLA\.MI04\.\w+)' depends on axioms: \[([^\]]*)\]",log)
assert [x[0] for x in prints]==names
assert all(set(x[1].split(', '))==set(config['permitted_axioms']) for x in prints)
assert log.count('declaration uses `sorry`')==21 and not re.search(r'warning: (?:Solution|NLA/MI04/).*declaration uses `sorry`',log)
assert 'Running Lean default kernel on solution.' in log and 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log
assert 'sorryAx' not in log and 'error:' not in log
built=set(re.findall(r'Built (NLA\.MI04\.\w+) \(',log))
assert built=={p[:-5].replace('/','.') for p in math if p.startswith('NLA/')}
assert len(built)==20 and 'Built Solution (' in log
checks={
 'reviewer':'/root/ie13_continuation','role':'Independent nonauthor evidence/source audit; no Lean execution by reviewer',
 'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'verdict':'APPROVED exact canonical runtime evidence',
 'run_id':35150473054,'job_id':104977317684,'literal_commit':HEAD,'project_inputs_matching_literal_Git':233,
 'math_sources_identical_to_prior_independently_reviewed_local_candidate':21,
 'math_source_map':math,'public_exports_and_permitted_axiom_reports':21,'actual_MI_modules_built':20,'actual_Solution_built':True,
 'frozen_original_snapshots':10,'active_frozen_exact':9,'only_active_frozen_config_transition':'defaultTargets Challenge -> Solution; exact prior snapshot retained',
 'dependent_package_pins':pins,'LeanCert_certificate_consumed':True,
 'manual_complete_log_review':'All twelve logs: Comparator, seven other verification/control/dependency logs, cache, and three bootstrap logs. No excerpt-only acceptance.',
 'actual_default_kernel_and_Comparator_accept':True,'actual_negative_sorry_and_native_reject':True,
 'controls':'Three default-kernel controls; five Comparator regressions; two forbidden-axiom cases; namespace/nonroot/read-only/AF_UNIX/isolation probes; service probe. All required per-proof groups ran.',
 'separate_checker_controls_job':'Skipped for this push; actual per-proof controls above ran in verify job.',
 'raw_log_correspondence':correspondence,'normalization':'Remove GitHub timestamp, ANSI display escapes, blank lines, artifact command header and recorded EXIT_STATUS footer; complete remaining payload equals exact contiguous job block.',
 'zip_members_byte_identical_to_extracted':13,'artifact_id':10468904090,'artifact_sha256':sha(zdata),
 'legacy_helper_invocation':{'script_sha256':bindings[str(B/'audit_canonical_runtime.py')], 'exit_code':0,'ROOT_AUDIT_sha256':bindings[str(P/'ROOT-AUDIT.json')], 'note':'Actually invoked by this reviewer; helper retains hardcoded /root reviewer label and matched its preexisting identical result. This own review supplies actual independent identity.'},
 'prior_independent_review_manifest_sha256':bindings[str(prior/'MANIFEST.json')],
 'limitations':['Audit of retained authenticated GitHub API/job/artifact evidence, not a second independently executed Lean run.',
  'Prior local Quadratic receipt omission remains historical; this canonical run actually builds Quadratic afresh.',
  'The checker explicitly performs no semantic review; full-target fidelity rests on separately retained independent source/statement reviews, extended here by exact byte equality.',
  'A subsequent publication commit and upstream PR merge checkout require their own exact-source/runtime checks; this acceptance is only literal 63340ef.'],
 'audit_development_note':'Initial unpublished payload prototype stopped at an internal Running line in comparator-controls; corrected to actual Running + Log command boundaries before acceptance. No proof/execution result was changed.',
 'no_compiler_Git_or_canonical_mutation':True,'count_delta':0}
(OUT/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
(OUT/'SOURCE-BINDINGS.json').write_text(json.dumps(bindings,indent=2,sort_keys=True)+'\n')
(OUT/'GIT-INPUTS.json').write_text(json.dumps({'commit':HEAD,'project':REL.rstrip('/'),'sha256':gitmap},indent=2,sort_keys=True)+'\n')
print(json.dumps({'passed':True,'external_bindings':len(bindings),'project_inputs':len(inputs),'math_sources':len(math),'logs_matched':len(correspondence),'zip_members':13}))

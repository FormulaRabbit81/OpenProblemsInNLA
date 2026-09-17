from pathlib import Path
import datetime, hashlib, json, re, subprocess, zipfile
B=Path('/tmp/nla-lean-next-20260915')
P=B/'canonical-runs/MF07-35172783207'; A=P/'artifacts/lean-MF-07'; E=A/'verify-20260917T021414Z-4149'
OUT=Path(__file__).parent
REPO=Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
HEAD='b2b9acc83ad7d6b7d3888de8390475a30c720af8'; REL='matrix-functions-and-stability/MF-07/lean/'
bindings={}; gitmap={}
def sha(b): return hashlib.sha256(b).hexdigest()
def read(p):
 b=Path(p).read_bytes(); bindings[str(p)]=sha(b); return b
def js(p):return json.loads(read(p))
def meta_repository(r):return r['repository']['full_name']
def blob(p):
 b=subprocess.check_output(['git','-C',str(REPO),'show',HEAD+':'+REL+p]); gitmap[p]=sha(b); return b
r=js(E/'result.json'); run=js(P/'run.json'); jobs=js(P/'jobs.json'); artifacts=js(P/'artifacts.json')
identity=js(P/'FETCH-IDENTITY.json'); generic=js(P/'ROOT-AUDIT.json')
read(B/'audit_canonical_runtime.py')
assert bindings[str(P/'ROOT-AUDIT.json')]=='d97ac2a9669ce2b4fe5ecb84e69cc2b2941ae2e35d1c099366dbcb80e77c7f79'
assert bindings[str(B/'audit_canonical_runtime.py')]=='77bcb3744ddb210972f82784be94001c9c7be34d26b3dc7b4d539dbc07352602'
assert run['id']==35172783207 and run['head_sha']==HEAD and run['status']=='completed' and run['conclusion']=='success'
assert r['repository_commit']==HEAD and r['project']==REL.rstrip('/') and r['result']=='comparator-accepted'
assert r['semantic_review']=='not-performed-by-this-command'
inputs=r['input_sha256']
paths=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','--name-only',HEAD,'--',REL],text=True).splitlines()
assert len(inputs)==297 and {p[len(REL):] for p in paths}==set(inputs)
for p,h in inputs.items():assert sha(blob(p))==h,p
local=js(B/'MF07-LOCAL-DEVELOPMENT-ACCEPTANCE.json')
prior=B/'reviews/MF07-ie13-final-local-development13'; prior_manifest=js(prior/'MANIFEST.json')
assert sha((prior/'MANIFEST.json').read_bytes())=='cbb50962347378f55cbf1b16e814f3b55811de70a65609bcfd28e5f90b342898'
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
assert 'import Challenge' not in solution and 'import NLA.MF07.Final' in solution
freeze=json.loads(blob('STATEMENT-FREEZE.json')); frozen=freeze['frozen_files_sha256']
assert frozen==local['frozen_files_sha256'] and len(frozen)==10
for p,h in frozen.items():assert sha(blob(freeze['snapshot_directory']+'/'+p))==h,p
for p,h in frozen.items():
 if p!='lakefile.toml': assert sha(blob(p))==h,p
oldlake=blob(freeze['snapshot_directory']+'/lakefile.toml'); newlake=blob('lakefile.toml')
assert oldlake.replace(b'defaultTargets = ["Challenge"]',b'defaultTargets = ["Solution"]')+b'\n[[lean_lib]]\nname = \"Solution\"\n'==newlake
transition=json.loads(blob('verification/packaging/TRANSITION.json'))
assert transition['proof_name_transport']=='Complete -> Solution with unchanged contents'
config=json.loads(blob('comparator.json'));assert config==r['config']
names=config['theorem_names'];assert len(names)==18 and len(set(names))==18
assert names==freeze['statement_names']
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound'] and config['definition_names']==[]
assert re.findall(r'^#print axioms (\S+)',solution,re.M)==freeze['statement_names']
assert re.findall(r'^#assert_trust kernel (\S+)',solution,re.M)==freeze['statement_names']
numerical=blob('NLA/MF07/Numerical.lean').decode()
assert 'interval_decide (trust := kernel)' in numerical and 'exp_one_bound m' in numerical
assert 'comparison_threshold_bound' in blob('NLA/MF07/Final.lean').decode()
manifest=json.loads(blob('lake-manifest.json'))
pins={x['name']:x['rev'] for x in manifest['packages']}
assert pins==local['dependency_commits'] and len(pins)==10
raw=read(P/'job-105047879291.log').decode()
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
zdata=read(P/'lean-MF-07.zip')
with zipfile.ZipFile(P/'lean-MF-07.zip') as z:
 members=z.namelist(); assert len(members)==len(set(members))==13
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in members)
 assert set(members)=={p.relative_to(A).as_posix() for p in A.rglob('*') if p.is_file()}
 for n in members:assert z.read(n)==read(A/n),n
artifact=next(x for x in artifacts['artifacts'] if x['id']==10478290606)
assert artifact['digest']=='sha256:'+sha(zdata) and artifact['workflow_run']['head_sha']==HEAD and not artifact['expired']
assert f'SHA256 digest of uploaded artifact zip is {sha(zdata)}' in raw
actualjobs={x['name']:x for x in jobs['jobs']}
verify=next(x for x in jobs['jobs'] if x['id']==105047879291)
assert verify['conclusion']=='success' and verify['head_sha']==HEAD
skip=next(x for x in jobs['jobs'] if x['id']==105047880091);assert skip['conclusion']=='skipped'
log=(E/'comparator.log').read_text()
prints=re.findall(r"info: Solution\.lean:\d+:0: '(NLA\.MF07\.\w+)' depends on axioms: \[([^\]]*)\]",log)
assert [x[0] for x in prints]==names
assert all(set(x[1].split(', '))==set(config['permitted_axioms']) for x in prints)
assert log.count('declaration uses `sorry`')==18 and not re.search(r'warning: (?:Solution|NLA/MF07/).*declaration uses `sorry`',log)
assert 'Running Lean default kernel on solution.' in log and 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log
assert 'sorryAx' not in log and 'error:' not in log
built=set(re.findall(r'Built (NLA\.MF07\.\w+) \(',log))
assert built=={p[:-5].replace('/','.') for p in math if p.startswith('NLA/')}
assert len(built)==20 and 'Built Solution (' in log
# The unchanged generic auditor is also actually run by this reviewer. Its output
# file already exists; it verifies exact equality rather than modifying the seal.
helper_output=subprocess.check_output(['python3',str(B/'audit_canonical_runtime.py'),str(P),'MF-07',REL.rstrip('/'),HEAD],text=True)
helper=json.loads(helper_output);assert helper['runtime_accepted'] and helper['root_audit_sha256']==bindings[str(P/'ROOT-AUDIT.json')]
# Preserve both original complete source reviews and canonical packaging scopes.
review_index=json.loads(blob('reviews/INDEX.json'))
final_review_bindings={}
for item in review_index['final_source_reviews']+review_index['canonical_package_reviews']:
    rel=Path(item['path']).parent.as_posix();d=B/'reviews'/Path(rel).name
    mh=item['manifest_sha256'];assert sha(read(d/'MANIFEST.json'))==mh
    assert sha(blob(rel+'/MANIFEST.json'))==mh
    inventory=js(d/'MANIFEST.json')
    for p,h in inventory['files'].items():
        digest=h['sha256'] if isinstance(h,dict) else h
        assert sha(read(d/p))==sha(blob(rel+'/'+p))==digest
    final_review_bindings[rel]=mh
# Selection really contains only this one project. The skipped standalone
# checker-controls job does not imply the per-proof controls were omitted.
selector=read(P/'job-105047812317.log').decode()
assert '{"include":[{"id":"MF-07","project":"matrix-functions-and-stability/MF-07/lean"}]}' in selector
assert meta_repository(run)=='sgstepaniants/OpenProblemsInNLA'
checks={
 'reviewer':'/root/ie13_continuation',
 'role':'Original MF07 statement-draft author; nonauthor of proof implementation; independent actual runtime-evidence/source-continuation audit, not a new rerun or independent review of own statement design',
 'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'verdict':'APPROVED exact MF07 canonical Linux runtime evidence',
 'run_id':35172783207,'job_id':105047879291,'literal_commit':HEAD,
 'project_inputs_matching_literal_Git':297,'math_sources_identical_to_prior_reviewed_local_candidate':21,
 'math_source_map':math,'public_exports_and_permitted_axiom_reports':18,
 'actual_MF07_modules_built':20,'actual_Solution_built':True,
 'frozen_original_snapshots':10,'active_frozen_exact':9,
 'only_active_frozen_transition':'Lake default Challenge -> Solution and addition of Solution library; exact original snapshot retained',
 'dependent_package_pins':pins,'LeanCert_certificate_consumed':True,
 'all_twelve_complete_logs_read':True,
 'actual_default_kernel_and_Comparator_accept':True,
 'actual_negative_sorry_and_native_reject':True,
 'controls':'Three builtin-kernel cases, five Comparator regressions, two forbidden-axiom cases, nonroot UID1001 build/export modes, namespace/read-only/AF_UNIX/nested-namespace/argument rejection and service probes all actually ran',
 'single_project_selection':'MF-07 only',
 'separate_checker_controls_job':'Skipped on this unchanged-harness push; all required per-proof controls ran in the verify job',
 'raw_log_correspondence':correspondence,
 'normalization':'Remove GitHub timestamps, ANSI display escapes, blank lines, artifact command header and recorded EXIT_STATUS footer; complete remaining payload equals exact contiguous raw job block',
 'zip_members_byte_identical_to_extracted':13,
 'artifact_id':10478290606,'artifact_sha256':sha(zdata),
 'shared_checker_unchanged_from':'ff6abf718126ceb23f933cf4f627f95104461fe8',
 'source_lock_sha256':r['source_lock_sha256'],
 'legacy_helper_invocation':{'script_sha256':bindings[str(B/'audit_canonical_runtime.py')],'exit_code':0,'ROOT_AUDIT_sha256':bindings[str(P/'ROOT-AUDIT.json')],
    'note':'Actually invoked by this reviewer; retained helper /root label is not a claim that this invocation was by root. Existing ROOT-AUDIT was verified byte-identical; own report provides actual reviewer identity.'},
 'original_full_source_and_packaging_reviews_preserved':final_review_bindings,
 'limitations':['Audit of authenticated retained GitHub API/job/artifact evidence, not another execution or a guarantee of checker infallibility.',
   'The command performs no semantic review; complete original-target fidelity rests on separately sealed statement and full-source reviews, preserved here by byte equality.',
   'This acceptance binds only literal proof commit b2b9acc83ad7d6b7d3888de8390475a30c720af8. A later publication commit/upstream merge requires its own exact-source/runtime checks.'],
 'no_Lean_Lake_cache_compiler_Git_or_canonical_mutation':True,'count_delta':0}
(OUT/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
(OUT/'SOURCE-BINDINGS.json').write_text(json.dumps(bindings,indent=2,sort_keys=True)+'\n')
(OUT/'GIT-INPUTS.json').write_text(json.dumps({'commit':HEAD,'project':REL.rstrip('/'),'sha256':gitmap},indent=2,sort_keys=True)+'\n')
print(json.dumps({'passed':True,'external_bindings':len(bindings),'project_inputs':len(inputs),'math_sources':len(math),'logs_matched':len(correspondence),'zip_members':13,'exports':18}))

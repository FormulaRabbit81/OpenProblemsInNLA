"""Prepared independent success-evidence audit. Run only on a terminal fetched packet.
This script audits an actual GitHub execution; it never invokes Lean or fetches data.
A successful script still requires the referee's complete manual log read and seal.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,zipfile
B=Path('/tmp/nla-lean-next-20260915');G=Path('/Users/georgestepaniants/Research/OpenProblemsInNLA');PROJECT='linear-systems-and-elimination/IE-13/lean';HEAD='032d4c86c52ffde0c4d440f28527ba43555a0a24';RUN=35081003513
R=Path(sys.argv[1]);O=Path(sys.argv[2]);S=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();H=lambda d:hashlib.sha256(d).hexdigest();J=lambda p:json.loads(p.read_text())
os.environ['GIT_OPTIONAL_LOCKS']='0'
def git(*a):return subprocess.check_output(['git','-c','gc.auto=0','-C',str(G),*a])
def put(n,v):(O/n).write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
meta=J(R/'run.json');assert meta['id']==RUN and meta['repository']['full_name']=='sgstepaniants/OpenProblemsInNLA' and meta['event']=='push' and meta['head_sha']==HEAD
assert meta['status']=='completed' and meta['conclusion']=='success','Do not infer acceptance from an incomplete or failed run'
assert not (O/'OPERATIONAL-CHECKS.json').exists(),'Do not overwrite a sealed audit'
receiptpaths=list((R/'artifacts/lean-IE-13').glob('verify-*/result.json'));assert len(receiptpaths)==1
rp=receiptpaths[0];e=rp.parent;result=J(rp);assert result['repository_commit']==HEAD and result['project']==PROJECT and result['result']=='comparator-accepted'
assert result['semantic_review']=='not-performed-by-this-command'
pkg=B/'IE13-canonical-package-v2';expected=dict(J(pkg/'PACKAGE-MANIFEST.json')['files']);expected['PACKAGE-MANIFEST.json']=S(pkg/'PACKAGE-MANIFEST.json');assert len(expected)==95
assert result['input_sha256']==expected
paths=git('ls-tree','-r','--name-only',HEAD,'--',PROJECT).decode().splitlines();assert set(paths)=={PROJECT+'/'+n for n in expected}
for n,h in expected.items():assert H(git('show',HEAD+':'+PROJECT+'/'+n))==h==S(pkg/n),n
config=J(pkg/'comparator.json');assert result['config']==config and not config['definition_names'];names=config['theorem_names'];assert len(names)==len(set(names))==28
standard={'propext','Classical.choice','Quot.sound'};assert set(config['permitted_axioms'])==standard
active=J(pkg/'ACTIVE-SOURCE-MANIFEST.json')['source_sha256'];assert len(active)==27 and all(expected[k]==v for k,v in active.items())
freeze=J(pkg/'STATEMENT-FREEZE.json')['frozen_files_sha256'];assert len(freeze)==10
for n,h in freeze.items():assert expected['verification/packaging/before/lakefile.toml' if n=='lakefile.toml' else n]==h
for prefix in ['tools/lean','docs/lean/schema','.github/workflows/lean-verification.yml','problem_ids.json','linear-systems-and-elimination/IE-13/README.md']:
 assert git('diff','ce47b5630bf3680d9211131c3a43825b022c139a',HEAD,'--',prefix)==b''
lock=git('show',HEAD+':tools/lean/source-lock.json');tool=result['tool_receipt'];assert H(lock)==result['source_lock_sha256']==tool['source_lock_sha256']
assert tool['platform'].startswith('Linux-') and tool['lean_toolchain']=='leanprover/lean4:v4.33.1' and 'x86_64-unknown-linux-gnu' in tool['lean_version']
assert tool['forsythe_commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert set(tool['executables'])=={'.tools/comparator/.lake/build/bin/comparator','.tools/lean4export/.lake/build/bin/lean4export','.tools/bin/landrun'}
for v in [tool['ci_sandbox_probe_sha256'],tool['env_sha256'],*tool['executables'].values()]:assert re.fullmatch('[0-9a-f]{64}',v)
logs={p.name:p.read_text() for p in e.glob('*.log')}
positive=['comparator.log','kernel-controls.log','comparator-controls.log','sandbox.log','dependencies.log','mathlib-cache.log','user-service.log']
assert set(logs)==set(positive)|{'negative-sorry.log','negative-native.log'}
for n in positive:assert logs[n].rstrip().endswith('EXIT_STATUS=0'),n
for n in ['negative-sorry.log','negative-native.log']:assert logs[n].rstrip().endswith('EXIT_STATUS=1'),n
comp=logs['comparator.log'];assert comp.index('Building Challenge')<comp.index('Building Solution')<comp.index('Running Lean default kernel on solution.')
assert comp.count('declaration uses `sorry`')==28 and 'declaration uses `sorry`' not in comp[comp.index('Building Solution'):]
assert all(s not in comp for s in ['sorryAx','Illegal axiom','error:'])
assert 'Lean default kernel accepts the solution' in comp and comp.count('Your solution is okay!')==1
for module in ['Challenge','Solution']:
 exports=[l for l in comp.splitlines() if l.startswith('Exporting #[') and l.endswith(' from '+module)];assert len(exports)==1
 assert re.findall(r'\bNLA\.[A-Za-z0-9_.]+',exports[0])==names
axioms={}
for name in names:
 reports=re.findall(re.escape("'"+name+"' depends on axioms: ")+r'\[([^\]]*)\]',comp);assert reports,name
 measured=[[a.strip() for a in report.split(',') if a.strip()] for report in reports];assert all(set(a)<=standard for a in measured),name;axioms[name]=measured
for rel in active:assert 'Built '+rel[:-5].replace('/','.')+' ' in comp,rel
assert "'NLA.IE13.half_bounds_certificate' depends on axioms:" in comp
for marker in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected:','RETURN quotient_postcheck_mismatch: rejected:','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
 assert marker in logs['kernel-controls.log'],marker
for name in ['simple_match','simple_mismatch','simple_axiom_issue','simple_kind_mismatch','type_mismatch']:assert 'PASS '+name+':' in logs['comparator-controls.log']
assert 'PASS: all five Comparator regressions' in logs['comparator-controls.log']
assert "Illegal axiom detected: 'sorryAx'" in logs['negative-sorry.log']
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in logs['negative-native.log']
sandbox=logs['sandbox.log'];assert re.findall(r'Sandbox UID: (\d+)',sandbox)==['1001','1001']
for marker in ['MODE build: exit=0','MODE export: exit=0','PASS effective capabilities: none','PASS AF_UNIX socket creation: denied','PASS no_new_privs: set','PASS user namespace: private','PASS pid namespace: private','PASS mnt namespace: private','PASS net namespace: private','PASS ipc namespace: private','PASS uts namespace: private','PASS export .lake write-open: denied','Outer and export fixture contents unchanged; only designated build fixture written.','NEGATIVE unknown option: exit=2','NEGATIVE unexpected --rw: exit=2','NEGATIVE unexpected --rwx: exit=2','NEGATIVE relative --rwx: exit=2','PASS nested namespace write attempt: rejected','PASS outside .lake write-open: denied','PASS host loopback listener: unreachable']:
 assert marker in sandbox,marker
for dep in J(pkg/'lake-manifest.json')['packages']:assert dep['rev'] in logs['dependencies.log'],dep['name']
jobs=J(R/'jobs.json')['jobs'];matches=[j for j in jobs if j['name']=='verify (IE-13, '+PROJECT+')'];assert len(matches)==1;job=matches[0]
assert job['conclusion']=='success' and all(s['conclusion'] in ['success','skipped'] for s in job['steps'])
select=next(j for j in jobs if j['name']=='select');assert select['conclusion']=='success'
rawpath=R/f"job-{job['id']}.log";raw=rawpath.read_text(encoding='utf-8-sig');assert re.search(r'git log -1 --format=%H\n[^\n]*'+HEAD+r'\n',raw)
rawlines=[re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?','',line) for line in raw.splitlines()]
logbindings=[]
for n,t in sorted(logs.items()):
 payload=[l for l in t.splitlines() if l and not l.startswith('$ ') and not l.startswith('EXIT_STATUS=')];pos=0
 for line in payload:
  while pos<len(rawlines) and rawlines[pos]!=line:pos+=1
  assert pos<len(rawlines),(n,line)
  pos+=1
 logbindings.append({'path':str((e/n).relative_to(R)),'sha256':S(e/n),'lines':len(t.splitlines()),'payload_lines':len(payload),'matches_actual_raw_job_in_order':True})
selectpath=R/f"job-{select['id']}.log";selectionraw=selectpath.read_text();assert PROJECT in selectionraw and '"id":"IE-13"' in selectionraw
assert 'Manifest schema and comparator coverage: PASS (28 declarations)' in raw
artifact=next(a for a in J(R/'artifacts.json')['artifacts'] if a['name']=='lean-IE-13');archive=R/'lean-IE-13.zip'
assert artifact['digest']=='sha256:'+S(archive) and not artifact['expired'];assert artifact['workflow_run']['id']==RUN and artifact['workflow_run']['head_sha']==HEAD
with zipfile.ZipFile(archive) as z:
 allmembers=[n for n in z.namelist() if not n.endswith('/')]
 for n in allmembers:
  assert not Path(n).is_absolute() and '..' not in Path(n).parts
  assert z.read(n)==(R/'artifacts/lean-IE-13'/n).read_bytes(),n
assert set(allmembers)=={str(f.relative_to(R/'artifacts/lean-IE-13')) for f in (R/'artifacts/lean-IE-13').rglob('*') if f.is_file()}
audit=J(R/'ROOT-AUDIT.json');assert audit['actual_checkout']==HEAD and audit['bound_inputs']==95 and audit['exports']==names and audit['literal_published_commit'] is True
assert audit['default_kernel_and_comparator']=='PASS' and audit['all_rejection_regression_sandbox_controls']=='PASS'
O.mkdir(parents=True,exist_ok=True)
put('OPERATIONAL-CHECKS.json',{'reviewer':'/root/mi04_independent_referee','verdict':'Actual canonical candidate evidence checks passed; complete manual log review and source-referee seal remain separate','actual_run':RUN,'job':job['id'],'api_head':meta['head_sha'],'receipt_checkout':HEAD,'literal_candidate':True,'all95_inputs_match_literal_Git_and_approved_package':True,'all27_math_frozen10_and28_exports_unchanged':True,'all28_observed_axiom_sets':axioms,'all9_log_payloads_match_raw_job_in_order':logbindings,'artifact_id':artifact['id'],'artifact_sha256':S(archive),'archive_members_exactly_match_extracted_files':len(allmembers),'receipt_sha256':S(rp),'source_lock_sha256':H(lock),'actual_default_kernel_and_Comparator':True,'actual_per_project_rejection_regression_and_sandbox_controls':True,'actual_nonroot_build_export_UIDs':[1001,1001],'shared_ROOT_AUDIT_fixed_reviewer_label':'The shared auditor has a fixed /root label; the executing actor must be disclosed in the final review and is not inferred from this field.','local_Lean_network_Git_mutation_count_change':False,'raw_job_sha256':S(rawpath),'full_selected_job_sha256':S(selectpath)})
put('ALL-95-INPUTS.json',expected)
print('Actual terminal IE13 canonical evidence checks passed; all95 inputs, 27-source graph, 28 exports, default kernel, controls and raw-log matching checked. Manual log review/seal still required.')

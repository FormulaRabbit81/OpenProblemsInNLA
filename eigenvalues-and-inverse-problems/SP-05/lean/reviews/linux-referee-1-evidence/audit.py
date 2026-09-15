from pathlib import Path
import ast,hashlib,json,re,shlex,subprocess,zipfile

repo=Path('/private/tmp/nla-formalization-sp05-20260915')
project=repo/'eigenvalues-and-inverse-problems/SP-05/lean'
archive=project/'verification/linux-2026-09-15'
raw=archive/'verify-20260915T221936Z-4220'
scratch=Path(__file__).parent
forsythe=Path('/private/tmp/nla-campaign-api-review/Forsythe')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
blobsha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda p:json.loads(p.read_text())
checks=[]
def check(name,value):
    assert value,name
    checks.append(name)
receipt=load(raw/'result.json');commit=receipt['repository_commit']
check('expected exact proof commit',commit=='9c8369dcea69f9f243a0502fb7e89beaa8f49fad')
run=load(scratch/'github-run.json');artifact=load(scratch/'github-artifact.json');job=load(scratch/'github-job.json')
check('independent GitHub run provenance',run['id']==35030259545 and run['head_sha']==commit and run['run_attempt']==1 and run['conclusion']=='success')
check('independent GitHub artifact provenance',artifact['id']==10421646579 and artifact['workflow_run']['id']==run['id'] and artifact['workflow_run']['head_sha']==commit and not artifact['expired'])
check('independent GitHub job provenance',job['id']==104586964871 and job['run_id']==run['id'] and job['head_sha']==commit and job['run_attempt']==1 and job['conclusion']=='success')
for step in ['Validate formalization manifest','Prepare unprivileged Linux isolation','Fresh sandboxed statement, axiom and kernel verification','Retain verification logs']:
    check('actual successful job step '+step,any(s['name']==step and s['conclusion']=='success' for s in job['steps']))
check('GitHub ZIP digest and size',artifact['digest']=='sha256:'+sha(archive/'lean-SP-05.zip') and artifact['size_in_bytes']==(archive/'lean-SP-05.zip').stat().st_size)
for key in ['id','head_sha','run_attempt','conclusion']:
    check('retained run field '+key,load(archive/'run-provenance.json')[key]==run[key])
check('retained artifact digest',load(archive/'artifact-provenance.json')['digest']==artifact['digest'])
retained_job=load(archive/'job-provenance.json')
for key,value in job.items(): check('retained job field '+key,retained_job[key]==value)
sealed={}
for line in (archive/'SHA256SUMS').read_text().splitlines():
    want,name=line.split('  ',1);check('archive SHA256 '+name,sha(archive/name)==want);sealed[name]=want
check('seventeen sealed archive members',len(sealed)==17)
check('checksum archive inventory complete',set(sealed)=={p.relative_to(archive).as_posix() for p in archive.rglob('*') if p.is_file() and p.name!='SHA256SUMS'})
zipmembers={}
with zipfile.ZipFile(archive/'lean-SP-05.zip') as z:
    names=[n for n in z.namelist() if not n.endswith('/')]
    check('thirteen unique ZIP members',len(names)==len(set(names))==13)
    check('ZIP member set is exactly retained logs and receipt',set(names)=={p.relative_to(archive).as_posix() for p in archive.rglob('*.log')}|{raw.relative_to(archive).as_posix()+'/result.json'})
    for name in names:
        check('authenticated extracted ZIP member '+name,z.read(name)==(archive/name).read_bytes())
        zipmembers[name]=blobsha(z.read(name))
for name,want in receipt['input_sha256'].items():
    check('current reviewed source '+name,sha(project/name)==want)
    data=subprocess.check_output(['git','show',commit+':'+receipt['project']+'/'+name],cwd=repo)
    check('committed receipt input '+name,blobsha(data)==want)
check('92 input hashes',len(receipt['input_sha256'])==92)
for record in ['reviews/statement-freeze.json','reviews/final-source-inputs.json']:
    for name,want in load(project/record)['input_sha256'].items():
        check('prior review matches receipt '+record+' '+name,receipt['input_sha256'][name]==want)
context=load(project/'reviews/final-referee-1-evidence/audit.json')['source_sha256']
for name,want in context.items():
    check('original source and review context unchanged '+name,sha(repo/name)==want)
lock=load(repo/'tools/lean/source-lock.json');tool=receipt['tool_receipt']
check('source lock exactly identified',sha(repo/'tools/lean/source-lock.json')==receipt['source_lock_sha256']==tool['source_lock_sha256'])
check('pinned Forsythe commit',lock['commit']==tool['forsythe_commit']==subprocess.check_output(['git','rev-parse','HEAD'],cwd=forsythe,text=True).strip())
for f in lock['files']:
    p=forsythe/f['source'];check('locked checker source '+f['source'],sha(p)==f['sha256'] and p.stat().st_size==f['bytes'])
for name in ['tools/lean/harness.py','tools/lean/source-lock.json','.github/workflows/lean-verification.yml']:
    check('executed infrastructure unchanged '+name,sha(repo/name)==blobsha(subprocess.check_output(['git','show',commit+':'+name],cwd=repo)))
src=ast.parse((repo/'tools/lean/harness.py').read_text())
fn=next(n for n in src.body if isinstance(n,ast.FunctionDef) and n.name=='ci_probe_source')
namespace={'Path':Path,'HarnessError':RuntimeError}
exec(compile(ast.Module(body=[fn],type_ignores=[]),'reviewed_ci_probe_function','exec'),namespace)
probe=namespace['ci_probe_source'](forsythe/'lean-proof')
check('exact adapted CI sandbox probe hash',blobsha(probe.encode())==tool['ci_sandbox_probe_sha256'])
main=(raw/'comparator.log').read_text()
args=shlex.split(main.splitlines()[0][2:]);i=args.index('/usr/bin/env')+2;environment={}
while '=' in args[i]:
    k,v=args[i].split('=',1);environment[k]=v;i+=1
probe_keys={'PATH','COMPARATOR_BIN','COMPARATOR_LEAN4EXPORT','COMPARATOR_LANDRUN','XDG_CACHE_HOME','TMPDIR'}
envtext='# Generated by the NLA pinned-tool bootstrap.\n'+'\n'.join('export '+k+'='+shlex.quote(v) for k,v in environment.items() if k in probe_keys)+'\n'
check('actual invocation reconstructs sealed probe environment',blobsha(envtext.encode())==tool['env_sha256'])
check('real strict sandbox selected',environment['COMPARATOR_LANDRUN'].endswith('/scripts/strict_landrun.py'))
check('actual comparator path matches receipt',environment['COMPARATOR_BIN'].endswith('/.tools/comparator/.lake/build/bin/comparator') and '.tools/comparator/.lake/build/bin/comparator' in tool['executables'])
check('actual exporter path matches receipt',environment['COMPARATOR_LEAN4EXPORT'].endswith('/.tools/lean4export/.lake/build/bin/lean4export') and '.tools/lean4export/.lake/build/bin/lean4export' in tool['executables'])
check('outer actual AF_UNIX restriction',"RestrictAddressFamilies=~AF_UNIX" in main.splitlines()[0])
check('config exact and six targets',receipt['config']==load(project/'comparator.json') and len(receipt['config']['theorem_names'])==6)
check('only permitted axioms',set(receipt['config']['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
exports=[line for line in main.splitlines() if line.startswith('Exporting #[')]
check('two actual exports',len(exports)==2 and exports[0].endswith('from Challenge') and exports[1].endswith('from Solution'))
for name in receipt['config']['theorem_names']:
    check('both exports cover '+name,all(name in line for line in exports))
    check('raw transitive axiom closure '+name,"'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in main)
check('trusted Challenge exported before Solution build',main.index(exports[0])<main.index('Building Solution'))
check('main kernel and Comparator success with exit zero','Lean default kernel accepts the solution\nYour solution is okay!' in main and main.endswith('EXIT_STATUS=0\n'))
check('fresh Solution built with no sorry warning','declaration uses `sorry`' not in main.split('Building Solution',1)[1] and 'Built NLA.SP05.Proof' in main and 'Built Solution' in main)
logs={p.relative_to(archive).as_posix():p.read_text() for p in archive.rglob('*.log')}
check('twelve complete raw logs inspected',len(logs)==12)
for name,content in logs.items():
    expected='1' if name.endswith(('negative-native.log','negative-sorry.log')) else '0'
    check('expected phase exit '+name,content.endswith('EXIT_STATUS='+expected+'\n'))
klog=(raw/'kernel-controls.log').read_text()
for marker in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected:','(kernel) declaration type mismatch','RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
    check('kernel control '+marker,marker in klog)
reg=(raw/'comparator-controls.log').read_text()
for name in ['simple_match','simple_mismatch','simple_axiom_issue','simple_kind_mismatch','type_mismatch']:
    check('Comparator regression '+name,('CASE '+name+'\n') in reg and ('PASS '+name+':') in reg)
for name,marker in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
    check('real negative proof rejection '+name,marker in (raw/name).read_text())
sandbox=(raw/'sandbox.log').read_text()
for marker in ['MODE build: exit=0','MODE export: exit=0','PASS outside .lake write-open: denied','PASS outside .lake truncate: denied','PASS outside .lake read-only truncate-open: denied','PASS symlink from .lake to outside write: denied','PASS outside .lake creation: denied','PASS build .lake write: allowed','PASS export .lake write-open: denied','PASS export .lake truncate: denied','PASS host parent: absent from private /proc','PASS host parent signal lookup: denied','PASS host loopback listener: unreachable','PASS AF_UNIX socket creation: denied','PASS effective capabilities: none','PASS no_new_privs: set','PASS nested namespace write attempt: rejected','NEGATIVE unknown option: exit=2','NEGATIVE unexpected --rw: exit=2','NEGATIVE unexpected --rwx: exit=2','NEGATIVE relative --rwx: exit=2','Outer and export fixture contents unchanged; only designated build fixture written.']:
    check('real sandbox probe '+marker,marker in sandbox)
for ns in ['user','pid','mnt','net','ipc','uts']:
    check('private namespace both modes '+ns,sandbox.count('PASS '+ns+' namespace: private')==2)
deps=(raw/'dependencies.log').read_text()
for p in load(project/'lake-manifest.json')['packages']:
    check('fresh dependency '+p['name'],"checking out revision '"+p['rev']+"'" in deps)
check('separate checker-controls independently confirmed skipped',next(j for j in load(scratch/'github-jobs.json')['jobs'] if j['name']=='checker-controls')['conclusion']=='skipped')
check('individual retained job matches independent API',job==load(archive/'job-provenance.json'))
closures=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",main)
check('all 24 raw transitive closures printed',len(closures)==24)
for name,al in closures:
    check('all raw closure axioms permitted '+name,{x.strip() for x in al.split(',')}<={'propext','Classical.choice','Quot.sound'})
tree_entries=subprocess.check_output(['git','ls-tree','-r','-z',commit,'--',receipt['project']],cwd=repo).split(b'\0')
tracked={}
for entry in tree_entries:
    if not entry: continue
    meta,path=entry.split(b'\t'); mode,kind,oid=meta.decode().split(); name=path.decode()[len(receipt['project'])+1:]
    check('ordinary tracked snapshot input '+name,mode in {'100644','100755'} and kind=='blob' and '.lake' not in Path(name).parts and Path(name).suffix not in {'.olean','.ilean','.o','.so','.a'})
    tracked[name]=oid
check('receipt covers full exact Git project tree',set(tracked)==set(receipt['input_sha256']))
current_proof_set={f.relative_to(project).as_posix() for f in (project/'NLA').rglob('*.lean')}|{'Challenge.lean','Solution.lean'}
expected_proof_set={f for f in receipt['input_sha256'] if f.startswith('NLA/') and f.endswith('.lean')}|{'Challenge.lean','Solution.lean'}
check('no current unreviewed implementation module',current_proof_set==expected_proof_set)
check('proof commit descends from approved source candidate',subprocess.run(['git','merge-base','--is-ancestor','081423df8a2445285261bcef2edc8fd66945f200',commit],cwd=repo).returncode==0)
check('canonical still Solved before promotion','**Status:** Solved  ' in (project.parent/'README.md').read_text())
check('source review one sealed PASS',sha(project/'reviews/final-referee-1.md')=='b95a1710c7b0e59e64f83a35234cf878d1647552b0d22e6e9fd249939edbf533')
check('source review two sealed APPROVE',sha(project/'reviews/final-referee-2.md')=='7e280cda8973798381d9f5c02390a55e1b2e293a400173ace40edd0a8a17e036')
check('frozen ten and source twenty-three counts',len(load(project/'reviews/statement-freeze.json')['input_sha256'])==10 and len(load(project/'reviews/final-source-inputs.json')['input_sha256'])==23)
check('no definition holes or external kernel configuration',receipt['config']['definition_names']==[] and set(receipt['config'])=={'challenge_module','solution_module','theorem_names','definition_names','permitted_axioms'})
check('Lean toolchain exact pinned version',tool['lean_toolchain']==(project/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1')
check('raw fresh Challenge 2710 and Solution 3738 jobs','Build completed successfully (2710 jobs).' in main and 'Build completed successfully (3738 jobs).' in main)
check('six and only six intentional Challenge holes',main.split('Building Solution',1)[0].count('declaration uses `sorry`')==6)
for name in expected_proof_set-{'Challenge.lean'}:
    module=name[:-5].replace('/','.')
    check('actual fresh build each implementation module '+module,('Built '+module+' (') in main)
freeze=load(project/'reviews/statement-freeze.json')
for name,want in freeze['independent_statement_reports'].items():
    check('preproof independent approval seal '+name,sha(project/name)==want==receipt['input_sha256'][name])
check('candidate descends from preproof freeze',subprocess.run(['git','merge-base','--is-ancestor','04d1de395494800390405f3df1645316fe7943c2','081423df8a2445285261bcef2edc8fd66945f200'],cwd=repo).returncode==0)
check('canonical and registry exact published base',all((repo/name).read_bytes()==subprocess.check_output(['git','show','d8c38a795876b132c90df8d1be8682d3dcde394c:'+name],cwd=repo) for name in ['eigenvalues-and-inverse-problems/SP-05/README.md','problem_ids.json']))
check('target job Ubuntu 24.04 runner',job['labels']==['ubuntu-24.04'])
check('target job exact SP05 project',job['name']=='verify (SP-05, eigenvalues-and-inverse-problems/SP-05/lean)')
check('source module kernel certificate explicit mode and bound','interval_decide (trust := kernel)' in (project/'NLA/SP05/Certificates.lean').read_text() and '(0 : ℝ) < 2' in (project/'NLA/SP05/Certificates.lean').read_text())
report={'result':'PASS independent operational evidence audit','reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent AI; no proof implementation',
 'repository_commit':commit,'run_id':run['id'],'run_attempt':1,'job_id':job['id'],'artifact_id':artifact['id'],'artifact_sha256':sha(archive/'lean-SP-05.zip'),
 'input_sha256':receipt['input_sha256'],'all_input_files_match_current_and_commit':True,'frozen_and_final_source_review_inputs_match':True,'source_context_sha256':context,
 'locked_sources_count':len(lock['files']),'source_lock_sha256':receipt['source_lock_sha256'],'harness_sha256':sha(repo/'tools/lean/harness.py'),'workflow_sha256':sha(repo/'.github/workflows/lean-verification.yml'),
 'raw_evidence_sha256':{p.relative_to(archive).as_posix():sha(p) for p in sorted(archive.rglob('*')) if p.is_file()},'zip_member_sha256':zipmembers,
 'raw_transitive_axiom_closures':dict(closures),'tool_receipt':tool,'all_git_snapshot_paths_exact':True,'raw_logs_count':len(logs),'raw_logs_line_count':sum(len(s.splitlines()) for s in logs.values()),'checks':checks,'checks_count':len(checks),
 'independent_github_query_sha256':{p.name:sha(p) for p in scratch.glob('github-*.json')},
 'limits':'Audited the actual authenticated hosted Linux run; did not execute a second Linux run on this macOS host. Local proof review is separately sealed.'}
(scratch/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['result','checks_count','raw_logs_count','raw_logs_line_count','locked_sources_count','artifact_sha256']},indent=2))

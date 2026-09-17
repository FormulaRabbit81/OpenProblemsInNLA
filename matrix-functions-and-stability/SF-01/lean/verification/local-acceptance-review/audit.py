"""Authenticate existing SF01 local execution; never invoke Lean or mutate inputs."""
from pathlib import Path
from hashlib import sha256
import datetime, json, os, re, subprocess

B=Path('/tmp/nla-lean-next-20260915').resolve()
L=Path('/private/tmp/nla-lean-local-shared-20260916')
S=B/'next-proofs/SF-01'
R=B/'reviews/SF01-mi04-local16-acceptance'
R.mkdir(exist_ok=True)
OUT=B/'SF01-LOCAL-DEVELOPMENT-ACCEPTANCE.json'
assert not OUT.exists(), 'Do not overwrite an accepted record'
checks=[]; bindings={}; chains={}

def check(ok,label):
    if not ok: raise AssertionError(label)
    checks.append(label)

def sha(p):
    h=sha256()
    with Path(p).open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20),b''): h.update(chunk)
    return h.hexdigest()

def bind(p,expected=None):
    p=Path(p).resolve();check(p.is_file(),'file exists: '+str(p));h=sha(p)
    if expected is not None:check(h==expected,'SHA256: '+str(p))
    bindings[str(p)]=h
    return p

def read(p,expected=None):return json.loads(bind(p,expected).read_text())

ap=bind(L/'ASSEMBLY-16.json','f2436899865783cbd40f9c3e354c8ad9605e1f45c8e624c4d4e61d602b26af2d')
a=read(ap);rp=L/'runs/development-16/RECEIPT.json';r=read(rp)
check(bool(r.get('end')),'actual development16 terminal')
check(r['assembly_sha256']==sha(ap),'actual receipt names exact assembly16')
bind(L/'serial_compile_v3.py',r['runner_sha256'])
env=read(L/'LOCAL-ENVIRONMENT.json');bind(env['compiler'],r['compiler_sha256'])
check(r['platform']=='darwin' and r['max_compiler_processes']==r['threads']==1,'actual macOS serial one-thread execution')
check(r['memory_cap_mib']==4096,'actual disclosed memory cap4096MiB')

allmodules={p[:-5].replace('/','.'):p for p in a['sources']}
allimports={m:[d for line in (L/p).read_text().splitlines() if line.startswith('import ') for d in line[7:].split() if d.startswith('NLA.')] for m,p in allmodules.items()}
memo={};visiting=set()
def closure(m):
    if m in memo:return memo[m]
    check(m in allmodules and m not in visiting,'finite dependency graph: '+m)
    visiting.add(m)
    out={m}
    for d in allimports[m]:out.update(closure(d))
    visiting.remove(m);memo[m]=out;return out

final=closure('NLA.SF01.FinalChecks')
sf={m for m in allmodules if m.startswith('NLA.SF01.')}
selected=sf|final
probes=selected-final
check(len(sf)==35 and len(final)==31 and len(selected)==37,'35 SF inputs +2 adopted IV inputs; final closure31')
check(probes=={'NLA.SF01.AnalyticalChecks','NLA.SF01.FoundationChecks','NLA.SF01.PoleChecks','NLA.SF01.ResolventChecks','NLA.SF01.RidgeChecks','NLA.SF01.SpectralBridgeChecks'},'six exact historical probe wrappers outside final dependency closure')
sources={allmodules[m]:a['sources'][allmodules[m]]['sha256'] for m in sorted(selected)}
for p,h in sources.items():
    bind(L/p,h);bind(a['sources'][p]['source'],h)
    check(r['source_inputs'][p]==h,'receipt source input matches selected assembly: '+p)
check(not (final & set(r['failed_modules']+r['blocked_modules'])),'no failed or blocked SF/IV final-closure module')
check(set(m for m in r['module_order'] if m in selected)==final,'development16 ran exactly final31, not six earlier wrappers')

receipts={}
for p in sorted((L/'runs').glob('*/RECEIPT.json')):
    j=json.loads(p.read_text())
    if j.get('end'):receipts[p.resolve()]=j
olean=lambda m:L/'.lake/build/lib/lean'/(allmodules[m][:-5]+'.olean')

def source_compatible(j,m):
    return all((j.get('source_inputs',{}).get(allmodules[d]) if not isinstance(j.get('source_inputs',{}).get(allmodules[d]),dict) else j['source_inputs'][allmodules[d]].get('sha256'))==sources[allmodules[d]] for d in closure(m))

def origin(c,path,m,seen=None):
    path=Path(path).resolve();seen=set() if seen is None else seen
    token=(str(path),m,json.dumps(c,sort_keys=True))
    check(token not in seen,'acyclic actual command-origin chain: '+m);seen=seen|{token}
    j=read(path)
    check(j.get('end') and c in j.get('commands',[]),'actual command present in terminal receipt: '+m)
    check(source_compatible(j,m),'all transitive source hashes compatible in actual origin receipt: '+m)
    check(c['source_sha256']==sources[allmodules[m]],'actual command source identity: '+m)
    bind(olean(m),c['output_sha256'])
    chains.setdefault(m,[]).append({'receipt':str(path),'receipt_sha256':sha(path),'status':c.get('status','executed'),'source_sha256':c['source_sha256'],'output_sha256':c['output_sha256']})
    if c.get('status')=='reused_exact_successful_local_output':
        if 'prior_command' in c:
            candidates=[p for p,q in receipts.items() if c['prior_command'] in q.get('commands',[])]
            check(bool(candidates),'embedded historical command found in actual receipt: '+m)
            return origin(c['prior_command'],sorted(candidates)[0],m,seen)
        prior=bind(c['prior_receipt'],c['prior_receipt_sha256'])
        expect={allmodules[d]:sources[allmodules[d]] for d in closure(m)}
        check(c['transitive_source_hashes']==expect,'entire exact cached transitive closure: '+m)
        q=read(prior)
        candidates=[v for v in q.get('commands',[]) if v.get('module')==m and v.get('source_sha256')==c['source_sha256'] and v.get('output_sha256')==c['output_sha256']]
        check(len(candidates)==1,'unique prior successful command: '+m)
        return origin(candidates[0],prior,m,seen)
    check(c.get('exit_code')==0 and c.get('end'),'actual underlying command exit0: '+m)
    expected=[env['compiler'],'--threads=1',c['argv'][2],'-o',str(olean(m)),allmodules[m]]
    check(c['argv']==expected and c['argv'][2] in ['--memory=3072','--memory=4096'],'exact ordinary single-thread compiler command: '+m)
    check(Path(c['cwd']).resolve()==L.resolve(),'actual compiler working directory: '+m)
    log=bind(path.parent/(m+'.log'),c['log_sha256']);text=log.read_text()
    check(not re.search(r'(^|\n).*error(?:\(|:)',text),'no compiler error in successful actual log: '+m)
    deps=c.get('dependency_olean_sha256',{})
    check(set(deps)==set(allimports[m]),'complete direct local dependency output map: '+m)
    for d,h in deps.items():bind(olean(d),h)
    return {'receipt':str(path),'receipt_sha256':sha(path),'log':str(log),'log_sha256':sha(log),'exit_code':0,'source_sha256':c['source_sha256'],'output_sha256':c['output_sha256'],'argv':c['argv'],'dependency_olean_sha256':deps,'scope':'final dependency closure' if m in final else 'compatible prior historical probe; not rerun in development16'}

origins={}
for m in sorted(final):
    cs=[c for c in r['commands'] if c['module']==m]
    check(len(cs)==1,'one actual development16 command record: '+m)
    origins[m]=origin(cs[0],rp,m)
for m in sorted(probes):
    candidates=[]
    for p,j in receipts.items():
        if j['end']>r['end'] or not source_compatible(j,m):continue
        for c in j.get('commands',[]):
            if c.get('module')==m and c.get('source_sha256')==sources[allmodules[m]] and c.get('output_sha256')==sha(olean(m)) and c.get('exit_code')==0:
                candidates.append((p,c))
    check(bool(candidates),'compatible actual prior successful probe found: '+m)
    p,c=sorted(candidates,key=lambda x:str(x[0]))[-1]
    origins[m]=origin(c,p,m)

freeze=read(S/'STATEMENT-FREEZE.json')
check(len(freeze['frozen_files'])==9,'nine frozen original inputs')
for p,h in freeze['frozen_files'].items():bind(S/p,h)
comp=read(S/'comparator.json');names=comp['theorem_names']
check(len(names)==len(set(names))==24 and comp['definition_names']==[],'exact24 frozen declarations and no definition holes')
check(set(comp['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'},'three standard permitted axioms only')
wrapper=bind(L/'NLA/SF01/FinalChecks.lean').read_text()
check(re.findall(r'^namespace (\S+)',wrapper,re.M)==['NLA.SF01'],'FinalChecks uses exactly the frozen SF01 namespace')
check({'NLA.SF01.'+n for n in re.findall(r'^#print axioms (\S+)',wrapper,re.M)}==set(names),'FinalChecks prints all24 frozen axiom lists')
check(['NLA.SF01.'+n for n in re.findall(r'^#assert_trust kernel (\S+)',wrapper,re.M)]==names,'FinalChecks checks all24 with kernel trust')
check('import Challenge' not in wrapper,'actual final entrypoint does not import specification holes')
log=bind(origins['NLA.SF01.FinalChecks']['log']).read_text()
observed={name:[s.strip() for s in raw.split(',') if s.strip()] for name,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
check(len(observed)==24 and set(observed)==set(names),'24 measured final declarations exactly match frozen Comparator list')
check(all(v==['propext','Classical.choice','Quot.sound'] for v in observed.values()),'all24 measured axiom lists contain exactly permitted standard axioms')
numerical=bind(L/'NLA/SF01/Numerical.lean').read_text()
check('interval_decide (trust := kernel)' in numerical and 'NLA.SF01.Numerical' in origins,'actual successful local kernel LeanCert scalar certificate')

# Bounded independent review support for root-authored routine SF bodies.
repair_records=[]
repair_manifests={11:'f8d3d0802eeb327ce12e2ffd377b7091ddd14ac3b3eefa4591f70a96d2c2680d',13:'21a56ef3f22a2da4f604b000dc497a7d1647f6b2070232ee97a269f1e86c7e7e',14:'2d2a2e39c1005fe7d7727fb6b1f8e437887b4d6210e6ce566809892af4a43fb8',15:'250d8b8c1f00bbbd85ab51be6b86a1e0b78f8982b027e891e411d00d674b24df'}
for number,h in repair_manifests.items():
    packet=B/'local-routine-repairs'/('development'+str(number));pm=read(packet/'MANIFEST.json',h)
    for p,v in pm['files'].items():bind(packet/p,v)
    before_files=sorted((packet/'before/NLA/SF01').glob('*.lean.txt'))
    check(len(before_files)==1,'one bounded SF module per repair packet: '+str(number))
    before=before_files[0];after=packet/'after/NLA/SF01'/before.name
    bt=before.read_text();at=after.read_text();m='NLA.SF01.'+before.name.split('.')[0]
    headers=lambda text:re.findall(r'^\s*(?:(?:private|protected)\s+)?(?:theorem|lemma|def|abbrev)\s+[\s\S]*?\s:=',text,re.M)
    check(headers(bt)==headers(at),'all declaration headers unchanged in routine repair: '+m+'/'+str(number))
    directives=lambda text:[l for l in text.splitlines() if l.startswith(('import ','set_option ','namespace ','variable ','open ','noncomputable '))]
    check(directives(bt)==directives(at),'imports/options/section context unchanged: '+m+'/'+str(number))
    q=read(packet/'actual-terminal-receipt.json')
    check(sha(packet/'actual-terminal-receipt.json')==sha(L/'runs'/('development-'+str(number).zfill(2))/'RECEIPT.json'),'actual failed receipt unchanged: '+str(number))
    c=next(c for c in q['commands'] if c['module']==m)
    check(c['exit_code']!=0 and c['source_sha256']==sha(before),'repair before source equals actually failed command: '+m)
    bind(packet/(m+'.log'),c['log_sha256'])
    repair_records.append({'packet':str(packet),'manifest_sha256':h,'module':m,'before_sha256':sha(before),'after_sha256':sha(after),'failed_log_sha256':c['log_sha256'],'header_and_context_preserved':True})
check(sha(B/'local-routine-repairs/development11/after/NLA/SF01/ReciprocalBlocks.lean.txt')==sha(B/'local-routine-repairs/development13/before/NLA/SF01/ReciprocalBlocks.lean.txt'),'sequential ReciprocalBlocks routine repair continuity')
for module,n in [('ReciprocalBlocks',13),('PoleCompression',14),('NewtonConclusion',15)]:
    check(sha(B/'local-routine-repairs'/('development'+str(n))/'after/NLA/SF01'/(module+'.lean.txt'))==sources['NLA/SF01/'+module+'.lean'],'latest repaired source exactly assembled: '+module)

deps={};git_env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
for d in env['dependencies']:
    package=L/'.lake/packages'/d['package']
    rev=subprocess.check_output(['git','-c','gc.auto=0','-C',str(package),'rev-parse','HEAD'],text=True,env=git_env).strip()
    check(rev==d['commit'],'actual dependency revision: '+d['package'])
    status=subprocess.check_output(['git','-c','gc.auto=0','-C',str(package),'status','--porcelain','--untracked-files=no'],text=True,env=git_env)
    check(not status,'actual dependency tracked sources clean: '+d['package'])
    deps[d['package']]=rev
mathlib=L/'.lake/packages/mathlib'
for rel in ['Mathlib/LinearAlgebra/Matrix/Kronecker.lean','Mathlib/Data/Matrix/Mul.lean']:
    p=bind(mathlib/rel)
    raw=subprocess.check_output(['git','-c','gc.auto=0','-C',str(mathlib),'show',deps['mathlib']+':'+rel],env=git_env)
    check(sha256(raw).hexdigest()==sha(p),'routine repair primary API matches pinned Git object: '+rel)

for p,h in sources.items():bind(L/p,h)
accepted={('Solution.lean' if p=='NLA/SF01/FinalChecks.lean' else p):h for p,h in sources.items()}
locations={('Solution.lean' if p=='NLA/SF01/FinalChecks.lean' else p):a['sources'][p]['source'] for p in sources}
finalpaths={('Solution.lean' if allmodules[m]=='NLA/SF01/FinalChecks.lean' else allmodules[m]):sources[allmodules[m]] for m in sorted(final)}
probepaths={allmodules[m]:sources[allmodules[m]] for m in sorted(probes)}
result={'reviewer':'/root/mi04_independent_referee','time':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'role':'Operational auditor of existing local execution and nonauthor reviewer of four root routine repairs; author of BlockLiftAlgebra, therefore not a full independent SF01 source referee.',
 'scope':'Source-bound complete SF01 local macOS final dependency graph plus separately authenticated compatible prior check wrappers; canonical verification remains pending.',
 'complete_development_graph_passed':True,'frozen_export_count':24,'selected_source_count':37,'final_transitive_source_count':31,'historical_check_wrapper_count':6,
 'canonical_verification_completed':False,'comparator_run':False,'platform':r['platform'],'receipt':str(rp),'receipt_sha256':sha(rp),
 'assembly_sha256':sha(ap),'audit_script_sha256':sha(__file__),'compiler_sha256':r['compiler_sha256'],'max_compiler_processes':1,
 'accepted_source_sha256':accepted,'selected_source_locations':locations,'final_transitive_source_sha256':finalpaths,'historical_check_source_sha256':probepaths,
 'source_transport':'NLA/SF01/FinalChecks.lean -> Solution.lean with identical bytes; no other source renaming.',
 'observed_axioms':observed,'actual_commands':origins,'command_origin_chains':chains,'bindings':bindings,'dependency_commits':deps,'frozen_files_sha256':freeze['frozen_files'],
 'routine_repair_reviews':repair_records,'routine_repair_source_approval':True,'independent_complete_source_review':False,
 'unrelated_actual_failures':r['failed_modules'],'unrelated_actual_blocks':r['blocked_modules'],
 'limitations':['31 final transitive inputs are represented in the actual development16 command sequence. Six additional unchanged check wrappers were not rerun in that batch; their compatible exact-source and dependency-output successful earlier commands are independently bound.',
 'Dependencies use pinned shared compiled caches. This is not fresh Linux sandbox execution, default-kernel replay, Comparator or isolation/rejection controls. No publication commit or PR is accepted.',
 'The reviewer authored BlockLiftAlgebra; this operational audit and bounded nonauthor routine-repair review must not be represented as an independent complete mathematical review.',
 'LOCAL-ENVIRONMENT.json preserves its initial 2048MiB planning policy. Actual recorded compiler commands use 3072 or4096MiB, serially; no theorem heartbeat/resource setting is changed by this audit.'],
 'count_change':0}
OUT.write_text(json.dumps(result,indent=2)+'\n')
(R/'CHECKS.json').write_text(json.dumps({'checks_passed':len(checks),'checks':checks,'binding_count':len(bindings),'acceptance_sha256':sha(OUT),'new_Lean_execution':False,'canonical_verification':False,'independent_complete_source_review':False,'count_change':0},indent=2)+'\n')
(R/'BINDINGS.json').write_text(json.dumps({os.path.relpath(p,R):h for p,h in sorted(bindings.items())},indent=2)+'\n')
(R/'ACTUAL-COMMANDS.json').write_text(json.dumps(origins,indent=2)+'\n')
(R/'ROUTINE-REPAIRS.json').write_text(json.dumps(repair_records,indent=2)+'\n')
(R/'DEPENDENCY-GRAPH.json').write_text(json.dumps({'final':sorted(final),'historical_check_wrappers':sorted(probes),'imports':{m:allimports[m] for m in sorted(selected)}},indent=2)+'\n')
print(json.dumps({'acceptance':str(OUT),'sha256':sha(OUT),'checks':len(checks),'bindings':len(bindings),'actual_successful_commands':len(origins),'final_closure':len(final),'historical_probes':len(probes),'measured_axiom_lists':len(observed)},indent=2))

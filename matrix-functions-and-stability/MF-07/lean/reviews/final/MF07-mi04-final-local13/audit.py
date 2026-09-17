from pathlib import Path
import datetime, hashlib, json, os, re, subprocess

B = Path('/tmp/nla-lean-next-20260915').resolve()
L = Path('/private/tmp/nla-lean-local-shared-20260916')
S = B / 'next-statements/MF-07'
P = B / 'reviews/MF07-mi04-complete-35071348416'
O = B / 'reviews/MF07-mi04-final-local13'
M = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib').resolve()
D = Path('/private/tmp/nla-lean-next-development-worktree')
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
checks, bindings = [], {}
def digest(b): return hashlib.sha256(b).hexdigest()
def ck(name, truth):
    checks.append({'check': name, 'pass': bool(truth)})
    if not truth: raise AssertionError(name)
def bind(path):
    path = Path(path).resolve(); data = path.read_bytes()
    bindings[os.path.relpath(path, O)] = {'sha256': digest(data), 'bytes': len(data)}
    return data
def read(path): return json.loads(bind(path))
def save(name, value):
    (O/name).write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')
def git(repo, *args):
    return subprocess.check_output(['git','-c','gc.auto=0','-C',str(repo),*args],
        env={**os.environ,'GIT_OPTIONAL_LOCKS':'0'})
def code(text):
    out=[]; i=0; nesting=0
    while i < len(text):
        if text[i:i+2]=='/-': nesting+=1; i+=2
        elif nesting and text[i:i+2]=='-/': nesting-=1; i+=2
        elif nesting:
            out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i); i=len(text) if j<0 else j
        else: out.append(text[i]); i+=1
    assert nesting==0
    return ''.join(out)
def headers(text):
    text=code(text); result={}
    for m in re.finditer(r'(?m)^(?:@\[[^\n]*?\]\s*)?(?:private\s+)?(?:noncomputable\s+)?(?:lemma|theorem|def|abbrev)\s+([^\s:{(]+)',text):
        i=m.start(); depth=0; k=i
        while k<len(text):
            ch=text[k]
            if ch in '({[': depth+=1
            elif ch in ')}]': depth-=1
            if depth==0 and text[k:k+2]==':=': break
            k+=1
        assert k<len(text),m.group(1)
        result[m.group(1)]=' '.join(text[i:k+2].split())
    return result
ck('new independent report directory',not O.exists()); O.mkdir(parents=True)
a=read(L/'ASSEMBLY-13.json'); r=read(L/'runs/development-13/RECEIPT.json')
ck('literal assembly receipt binding',r['assembly_sha256']==digest(bind(L/'ASSEMBLY-13.json')))
ck('actual terminal run, MF07 no failed or blocked module',bool(r['end']) and not any(x.startswith('NLA.MF07.') for x in r['failed_modules']+r['blocked_modules']))
selected={k:v for k,v in a['sources'].items() if k.startswith('NLA/MF07/')}
ck('twenty mathematical files plus exact export wrapper',len(selected)==21)
sources, delta, old_headers, current_headers, alpha_changes = {}, [], {}, {}, []
for path, rec in selected.items():
    data=bind(rec['source']); current=bind(L/path)
    ck('exact immutable selection/local/receipt '+path,digest(data)==rec['sha256']==r['source_inputs'][path] and current==data)
    if rec['origin'].startswith('literal '):
        ck('literal development Git input '+path,data==git(D,'show',a['base_commit']+':.lean-development/'+path))
    out=O/'sources'/path; out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(data)
    sources[path]={'source':os.path.relpath(Path(rec['source']).resolve(),O),'sha256':digest(data),'lines':len(data.splitlines())}
    text=data.decode(); h=headers(text); current_headers.update({k:{'path':path,'header':v} for k,v in h.items()})
    old=P/'sources'/path
    if old.exists():
        old_data=bind(old); oh=headers(old_data.decode()); old_headers.update({k:{'path':path,'header':v} for k,v in oh.items()})
        expected=dict(oh)
        if path=='NLA/MF07/SingularCoordinates.lean':
            name='ordered_positive_gram_coordinates'
            if oh[name]!=h[name]:
                expected[name]=oh[name].replace('λ','lam')
                alpha_changes.append({'path':path,'name':name,'before':oh[name],'after':h[name],
                    'scope':'Only the existing bound eigenvalue function name changes from lambda to lam; no public contract change.'})
        ck('all existing declaration propositions preserved '+path,expected==h)
        delta.append({'path':path,'old_sha256':digest(old_data),'new_sha256':digest(data),'changed':old_data!=data})
    else:
        ck('only export wrapper new since old full review',path=='NLA/MF07/Complete.lean')
    clean=code(text)
    ck('no admissions or trust bypass '+path,not re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide|implemented_by|unsafe)\b',clean))
    ck('no Challenge or other campaign imports '+path,all(not q.startswith('NLA.') or q.startswith('NLA.MF07.') for line in clean.splitlines() if line.startswith('import ') for q in line[7:].split()) and not re.search(r'^import .*Challenge',clean,re.M))
    ck('no additional section hypotheses '+path,not re.search(r'^\s*(variable|variables|axioms)\b',clean,re.M))
    ck('no resource relaxation '+path,not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth|debug|compiler|debug.skipKernelTC)',clean))
    if path!='NLA/MF07/Definitions.lean': ck('kernel trust setting '+path,'set_option leancert.trust "kernel"' in clean)
comparison_old={k:dict(v) for k,v in old_headers.items()}
comparison_old['ordered_positive_gram_coordinates']['header']=comparison_old['ordered_positive_gram_coordinates']['header'].replace('λ','lam')
ck('all original declarations present, only inspected helper alpha rename',len(old_headers)==len(current_headers) and comparison_old==current_headers and len(alpha_changes)==1)
imports={p:[q.replace('.','/')+'.lean' for line in code((O/'sources'/p).read_text()).splitlines() if line.startswith('import ') for q in line[7:].split() if q.startswith('NLA.')] for p in selected}
def closure(path,trail=()):
    ck('acyclic import '+path,path not in trail)
    return {path}|{x for dep in imports[path] for x in closure(dep,trail+(path,))}
ck('complete export dependency closure',closure('NLA/MF07/Complete.lean')==set(selected))
freeze=read(S/'STATEMENT-FREEZE.json'); frozen=freeze['frozen_files_sha256']
ck('ten frozen boundary files',len(frozen)==10)
for p,h in frozen.items(): ck('frozen byte identity '+p,digest(bind(S/p))==h)
comp=read(S/'comparator.json'); names=comp['theorem_names']
ck('eighteen exact names/no definition holes',len(names)==18 and not comp['definition_names'] and set(comp['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
previous_match=read(P/'STATEMENT-COMPARISON.json'); frozen_headers=headers((S/'Challenge.lean').read_text())
matches=[]
for old in previous_match:
    name=old['name'].split('.')[-1]; now=current_headers[name]
    ck('frozen contract and implementation header '+name,old['frozen_header']==frozen_headers[name] and old['implementation_header']==now['header'])
    matches.append({**old,'current_source_sha256':sources[now['path']]['sha256'],'same_as_previous_independent_full_review':True})
ck('public names match current header comparison',{x['name'] for x in matches}==set(names))
wrapper=(O/'sources/NLA/MF07/Complete.lean').read_text()
for command in ['check','print axioms','assert_trust kernel']:
    observed_names=re.findall(r'^#'+re.escape(command)+r'\s+(\S+)',wrapper,re.M)
    ck('all eighteen wrapper '+command,observed_names==names)

# Original target and the full manuscript are read privately, without copying
# the historical contact-bearing manuscript into this new review packet.
for rec in read(P/'ORIGINAL-TARGET-BINDINGS.json'):
    p=S/rec['packet_path']; data=bind(p)
    ck('original target identity '+rec['path'],digest(data)==rec['sha256'])
    ck('original target pinned Git blob '+rec['path'],data==git(D,'show',rec['commit']+':'+rec['path']))
for rec in read(P/'STANDARDS-BINDINGS.json'):
    p=S/rec['packet_path']; ck('retained scoped standards '+rec['path'],digest(bind(p))==rec['sha256'])
for rec in read(P/'PRIMARY-BINDINGS.json'):
    data=bind(rec['retained_path']);ck('previous exact pinned API '+rec['path'],digest(data)==rec['sha256'] and data==git(M,'show',PIN+':'+rec['path']))
primary=bind(M/'Mathlib/Data/Complex/Basic.lean')
ck('new exact inverse/coercion API',primary==git(M,'show',PIN+':Mathlib/Data/Complex/Basic.lean'))
ck('actual unconditional ofReal_inv theorem',b'theorem ofReal_inv (r :' in primary)

# Reconcile predecessor review seals, without copying unrelated histories.
predecessors=['MF07-mi04-complete-35071348416','MF07-mi04-unitary-followthrough-35071348416',
    'MF07-mi04-repair-35083895041','MF07-mi04-repair-35090376438','MF07-mi04-local-development09',
    'MF07-ie13-repair-local-development-02','MF07-ie13-repair-local-development-03',
    'MF07-ie13-repair-local-development07','MF07-ie13-repair-local-development10']
for name in predecessors:
    q=B/'reviews'/name; manifest=read(q/'MANIFEST.json'); report=bind(q/'REVIEW.md')
    file_rec=manifest.get('files',{}).get('REVIEW.md')
    if file_rec:
        expected=file_rec['sha256'] if isinstance(file_rec,dict) else file_rec
        ck('prior review seal '+name,digest(report)==expected)
routine=B/'local-routine-repairs/development11'
routine_manifest=read(routine/'MANIFEST.json')
for rel,info in routine_manifest.get('files',{}).items():
    expected=info['sha256'] if isinstance(info,dict) else info
    ck('routine observed-repair packet '+rel,digest(bind(routine/rel))==expected)
similarity_before=bind(routine/'before/NLA/MF07/Similarity.lean.txt')
similarity_after=bind(routine/'after/NLA/MF07/Similarity.lean.txt')
old_fragment='  change spectralNorm (diagonalWeights (fun i => (τ i)⁻¹)) ≤ 1\n'
new_fragment='  have he : inverseDiagonalWeights τ = diagonalWeights (fun i => (τ i)⁻¹) := by\n    simp only [inverseDiagonalWeights, diagonalWeights, Complex.ofReal_inv]\n  rw [he]\n'
ck('only typed real/complex inverse identity repair',similarity_before.decode().replace(old_fragment,new_fragment,1)==similarity_after.decode() and similarity_before.decode().count(old_fragment)==1)
ck('routine repaired candidate equals selected',digest(similarity_after)==sources['NLA/MF07/Similarity.lean']['sha256'])
bind(routine/'NLA.MF07.Similarity.log')

# Authenticate the actual existing local execution, not a new Lean run.
environment=read(L/'LOCAL-ENVIRONMENT.json')
ck('runner and compiler identity',digest(bind(L/'serial_compile_v3.py'))==r['runner_sha256'] and digest(bind(environment['compiler']))==r['compiler_sha256'])
ck('serial macOS execution scope',r['platform']=='darwin' and r['max_compiler_processes']==1 and r['threads']==1)
module_paths={p[:-5].replace('/','.'):p for p in selected}
receipts={p:json.loads(p.read_text()) for p in sorted((L/'runs').glob('*/RECEIPT.json'))}
origins={}
def actual_origin(command,receipt_path,module,seen=()):
    key=(module,digest(json.dumps(command,sort_keys=True).encode()))
    ck('no reuse cycle '+module,key not in seen)
    bind(receipt_path)
    ck('command source '+module,command['source_sha256']==sources[module_paths[module]]['sha256'])
    output=L/'.lake/build/lib/lean'/(module_paths[module][:-5]+'.olean')
    ck('current exact successful output '+module,digest(bind(output))==command['output_sha256'])
    if command.get('status')=='reused_exact_successful_local_output':
        if 'prior_command' in command:
            hits=[p for p,j in receipts.items() if j.get('end') and command['prior_command'] in j.get('commands',[])]
            ck('actual receipt contains embedded prior command '+module,bool(hits))
            return actual_origin(command['prior_command'],hits[0],module,seen+(key,))
        prior=Path(command['prior_receipt']); pj=read(prior)
        ck('literal prior receipt hash '+module,digest(bind(prior))==command['prior_receipt_sha256'])
        for path,h in command['transitive_source_hashes'].items(): ck('reuse transitive source '+path,h==sources[path]['sha256'])
        hits=[x for x in pj['commands'] if x.get('module')==module and x.get('source_sha256')==command['source_sha256'] and x.get('output_sha256')==command['output_sha256']]
        ck('unique underlying completed command '+module,bool(pj['end']) and len(hits)==1)
        return actual_origin(hits[0],prior,module,seen+(key,))
    ck('actual terminal success '+module,command['exit_code']==0 and bool(command['end']))
    ck('actual compiler command '+module,command['argv'][0]==environment['compiler'] and '--threads=1' in command['argv'] and any(x in command['argv'] for x in ['--memory=3072','--memory=4096']))
    log=receipt_path.parent/(module+'.log'); text=bind(log).decode()
    ck('literal compiler log '+module,digest(text.encode())==command['log_sha256'])
    ck('no errors/admission in successful log '+module,not re.search(r'(^|\n).*error(?:\(|:)',text) and 'sorryAx' not in text)
    for dep,h in command.get('dependency_olean_sha256',{}).items():
        output=L/'.lake/build/lib/lean'/(module_paths[dep][:-5]+'.olean')
        ck('actual dependency output '+dep,digest(bind(output))==h)
    return {'receipt':os.path.relpath(receipt_path,O),'receipt_sha256':digest(bind(receipt_path)),
        'source_sha256':command['source_sha256'],'output_sha256':command['output_sha256'],
        'log':os.path.relpath(log,O),'log_sha256':command['log_sha256'],'exit_code':0}
for module in module_paths:
    hits=[x for x in r['commands'] if x.get('module')==module]
    ck('unique final selected command '+module,len(hits)==1)
    origins[module]=actual_origin(hits[0],L/'runs/development-13/RECEIPT.json',module)
log=bind(L/'runs/development-13/NLA.MF07.Complete.log').decode()
axioms={name:[x.strip() for x in vals.split(',') if x.strip()] for name,vals in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
ck('all eighteen actual measured axioms',set(axioms)==set(names) and len(axioms)==18)
ck('all measured sets exactly standard axioms',all(set(v)=={'propext','Classical.choice','Quot.sound'} for v in axioms.values()))
dependencies={}
for rec in environment['dependencies']:
    pkg=L/'.lake/packages'/rec['package'];head=git(pkg,'rev-parse','HEAD').decode().strip()
    ck('current dependency exact pin '+rec['package'],head==rec['commit'])
    ck('dependency tracked source unchanged '+rec['package'],not git(pkg,'status','--porcelain','--untracked-files=no'))
    dependencies[rec['package']]=head
root_acceptance=read(B/'MF07-LOCAL-DEVELOPMENT-ACCEPTANCE.json')
ck('separate root local report source and run match',root_acceptance['assembly_sha256']==r['assembly_sha256'] and root_acceptance['observed_axioms']==axioms and not root_acceptance['comparator_run'])
for path,rec in sources.items():
    target='Solution.lean' if path.endswith('/Complete.lean') else path
    ck('separate root complete source agreement '+path,root_acceptance['accepted_source_sha256'][target]==rec['sha256'])
save('SOURCE-MAP.json',sources);save('SOURCE-CONTINUATION.json',{'all_public_headers_unchanged':True,'all_helper_propositions_preserved':True,'helper_alpha_renames':alpha_changes,'declarations':len(current_headers),'files':delta})
save('STATEMENT-COMPARISON.json',matches)
save('LOCAL-EVIDENCE.json',{'scope':'Independent audit of existing actual serial macOS execution; no new compiler invocation',
    'assembly_sha256':r['assembly_sha256'],'receipt_sha256':digest(bind(L/'runs/development-13/RECEIPT.json')),
    'successful_underlying_commands':origins,'measured_axioms':axioms,'dependency_commits':dependencies,
    'canonical_Linux_verification':False,'Comparator_execution':False,'new_Lean_execution':False,'count_change':0})
(O/'actual-Complete.log').write_text(log)
save('BINDINGS.json',bindings)
save('CHECKS.json',{'checks_passed':len(checks),'checks':checks,'binding_count':len(bindings),
    'full_read_lines':sum(v['lines'] for v in sources.values()),'mathematical_source_files':20,'export_wrapper_files':1,
    'source_approval':True,'local_execution_evidence_approval':True,'whole_problem_verification':False,'count_change':0})
(O/'audit.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'directory':str(O),'checks':len(checks),'bindings':len(bindings),'declarations':len(current_headers),'source_lines':sum(v['lines'] for v in sources.values()),'actual_successful_commands':len(origins)},indent=2))

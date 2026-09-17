#!/usr/bin/env python3
"""Independent read-only MI-13 source and retained runtime audit; never invokes Lean/Git."""
from pathlib import Path
import argparse, datetime, difflib, hashlib, json, re

args=argparse.ArgumentParser()
args.add_argument('--run',type=int,required=True)
run=args.parse_args().run
B=Path('/tmp/nla-lean-next-20260915')
P=B/'next-proofs/MI-13'
L=Path('/private/tmp/nla-lean-local-shared-20260916')
R=Path(__file__).resolve().parent
checks,bindings=[],{}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(n,c):
    if not c:raise AssertionError(n)
    checks.append(n)
def bind(p,h=None):
    p=Path(p).resolve();g=sha(p)
    check('bound bytes: '+str(p),h is None or h==g)
    check('stable repeated binding: '+str(p),str(p) not in bindings or bindings[str(p)]==g)
    bindings[str(p)]=g
    return g
def read(p):bind(p);return json.loads(Path(p).read_text())
def write(n,v):
    q=R/n;q.parent.mkdir(parents=True,exist_ok=True)
    q.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def copy(p,n):
    bind(p);q=R/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(Path(p).read_bytes())
def code(s):return re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
def manifest(d,known=None):
    d=Path(d);mp=d/'MANIFEST.json';bind(mp,known);v=read(mp);fs=v.get('files',v)
    check('manifest inventory: '+str(d),set(fs)=={str(q.relative_to(d)) for q in d.rglob('*')
        if q.is_file() and q!=mp})
    for rel,h in fs.items():
        digest=h['sha256'] if isinstance(h,dict) else h
        bind(d/rel,digest)
        if isinstance(h,dict) and 'bytes' in h:check('manifest byte count '+str(d/rel),(d/rel).stat().st_size==h['bytes'])
    return len(fs)

baseline=read(R/'SOURCE-READ-BASELINE.json')['files']
current={str(p.relative_to(P)):sha(p) for p in sorted(P.glob('NLA/MI13/*.lean'))+[P/'Solution.lean']}
check('22 independently read sources',len(current)==22 and set(current)==set(baseline))
changed=[rel for rel,h in current.items() if baseline[rel]!=h]
check('only documented final padding and circle reuse changes allowed',set(changed)=={'NLA/MI13/Padding.lean','NLA/MI13/ElementaryBounds.lean'})
continuations=[]
if 'NLA/MI13/Padding.lean' in changed:
    old=(R/'source-read-baseline/NLA/MI13/Padding.lean').read_text()
    new=(P/'NLA/MI13/Padding.lean').read_text()
    check('exact padding baseline source',hashlib.sha256(old.encode()).hexdigest()==baseline['NLA/MI13/Padding.lean'])
    check('only one unused zero_add argument removed',new==old.replace(
        'Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,',
        'Matrix.zero_mul, Matrix.mul_zero, add_zero,',1))
    continuations.append({'changed_file':'NLA/MI13/Padding.lean','before_sha256':baseline['NLA/MI13/Padding.lean'],
        'after_sha256':current['NLA/MI13/Padding.lean'],'exact_diff':''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='read-baseline',tofile='final')),
        'scope':'Independent reading of the sole unused-simp removal; no header, definition or route change.'})
circle=P/'proof-handoffs/circle-lemma-reuse-01'
old=(circle/'before.lean.txt').read_text();new=(circle/'after.lean.txt').read_text()
bind(circle/'before.lean.txt',baseline['NLA/MI13/ElementaryBounds.lean'])
bind(circle/'after.lean.txt',current['NLA/MI13/ElementaryBounds.lean'])
circle_diff=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='before',tofile='after'))
check('exact recorded circle reuse diff',circle_diff==(circle/'SOURCE-DIFF.patch').read_text())
a=old.index('theorem unit_circle_lift');b=old.index('theorem frobenius_average_bound')
c=new.index('theorem unit_circle_lift');d=new.index('theorem frobenius_average_bound')
check('only circle proof block changes',old[:a]==new[:c] and old[b:]==new[d:])
check('two exact pinned normSq APIs consumed','exact Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hdNorm' in new[c:d]
      and 'exact Complex.normSq_ofReal_sub_I_mul_sqrt_one_sub hdNorm' in new[c:d]
      and 'simpa only [Real.norm_eq_abs, abs_of_nonneg hd] using hd1' in new[c:d]
      and 'Real.sq_sqrt' not in new[c:d] and 'nlinarith' not in new[c:d])
continuations.append({'changed_file':'NLA/MI13/ElementaryBounds.lean','before_sha256':baseline['NLA/MI13/ElementaryBounds.lean'],
    'after_sha256':current['NLA/MI13/ElementaryBounds.lean'],'exact_diff':circle_diff,
    'scope':'Discharges independent full-review request by reusing the two exact Mathlib APIs; all headers and averaging certificate consumer unchanged.'})
write('FINAL-READ-CONTINUATION.json',continuations)
sources={};expected={};relative={};imports={};assertions={}
for rel,h in current.items():
    module=rel[:-5].replace('/','.')
    bind(P/rel,h);bind(L/rel,h);copy(P/rel,'evidence/final-source/'+rel)
    text=(P/rel).read_text();sources[module]=text;expected[module]=h;relative[module]=rel
    imports[module]=re.findall(r'^import (NLA\.MI13\.\S+)',text,re.M)
    assertions[module]=re.findall(r'^#print axioms (\w+)\s*$',text,re.M)
    check('trusted source mode '+module,module=='NLA.MI13.Definitions' or 'set_option leancert.trust "kernel"' in text)
    check('no proof bypass '+module,not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac|ofReduceBool)\b',code(text)))
    check('no Challenge import '+module,not re.search(r'^import .*Challenge\b',text,re.M))
    check('paired axiom/trust commands '+module,assertions[module]==re.findall(r'^#assert_trust kernel (\w+)\s*$',text,re.M))
    check('source attribution '+module,'George Stepaniants' in text and 'California Institute of Technology' in text)
for m,ds in imports.items():check('known project imports '+m,all(d in expected for d in ds))
def closure(m,seen=None):
    seen=set() if seen is None else seen
    check('acyclic project import '+m,m not in seen)
    out={m}
    for d in imports[m]:out|=closure(d,seen|{m})
    return out
check('Solution reaches all and only 22 proof inputs',closure('Solution')==set(expected))
freeze=read(P/'STATEMENT-FREEZE.json')
bind(P/'STATEMENT-FREEZE.json','bddc9d048f92e28dd8912f9bfb8293e12f07f2458fe7fb5a77e5b3c57e16e732')
check('13 frozen inputs',len(freeze['frozen_files'])==13)
for rel,h in freeze['frozen_files'].items():bind(P/rel,h);copy(P/rel,'evidence/frozen/'+rel)
headers=read(P/'STATEMENT-HEADERS.json')['declarations'];header_map=[]
challenge=(P/'Challenge.lean').read_text()
for item in headers:
    name=item['name'].split('.')[-1];pattern=r'\btheorem '+re.escape(name)+r'\b.*?(?=\s*:=\s*by\b)'
    frozen=re.search(pattern,challenge,re.S).group(0).rstrip()
    found=[(m,re.search(pattern,s,re.S)) for m,s in sources.items() if re.search(pattern,s,re.S)]
    check('exact one implementation of '+name,len(found)==1)
    m,match=found[0];header=match.group(0).rstrip()
    check('exact frozen header '+name,header==frozen==item['header'])
    check('frozen header digest '+name,hashlib.sha256(header.encode()).hexdigest()==item['header_sha256'])
    header_map.append({'name':item['name'],'module':m,'source_sha256':expected[m],
        'header_sha256':item['header_sha256'],'header':header})
names=[x['name'].split('.')[-1] for x in headers]
check('36 exact final trust exports',len(names)==36 and assertions['Solution']==names)
cfg=read(P/'comparator.json')
check('36 exact Comparator exports',cfg['theorem_names']==[x['name'] for x in headers]
      and cfg['challenge_module']=='Challenge' and cfg['solution_module']=='Solution'
      and cfg['definition_names']==[] and set(cfg['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
check('36 intentional independent Challenge holes',len(re.findall(r'\bsorry\b',code(challenge)))==36)
write('EXACT-HEADERS.json',header_map)
write('SOURCE-MAP.json',{'files':current,'imports':imports,'implementation_lines':sum(len(s.splitlines()) for s in sources.values()),
    'new_execution_by_reviewer':False,'no_Challenge_in_solution_closure':True})

acceptance=read(B/'MI13-ROOT-FREEZE-ACCEPTANCE.json')
check('separate root pre-proof acceptance',acceptance['freeze_sha256']==sha(P/'STATEMENT-FREEZE.json')
      and acceptance['source_boundary_changes'] is False and 'authorize proof implementation' in acceptance['verdict'])
copy(B/'MI13-ROOT-FREEZE-ACCEPTANCE.json','evidence/statement-acceptance/ROOT.json')
own_reviews={
 'MI13-prefix-second-referee-20260917':'0c17137ce4dc2297ee25723864a37a7114b95c98e19fa2fc933c58158ffc2c91',
 'MI13-operator-norm-referee-20260917':'8147a9cb207388ad04c50871a64fc5bcb10bb5ca811935804aac2f7f815d1260',
 'MI13-operator-norm-continuation-referee-20260917':'b35776edbae7130b7f62f5e3888239e6aed79d08b1de257d47ebb45a1c3ee9e0'}
prior_counts={}
for name,h in own_reviews.items():
    d=B/'reviews'/name;prior_counts[name]=manifest(d,h)
    for rel in ['MANIFEST.json','REVIEW.md','AUDIT.json']:
        copy(d/rel,'evidence/prior-own-reviews/'+name+'/'+rel)
cleanup=P/'proof-handoffs/prefix-cleanup-01';changes=read(cleanup/'CHANGES.json')
for m,item in changes['changes'].items():
    before=cleanup/f'before-{m}.lean.txt';after=cleanup/f'after-{m}.lean.txt'
    bind(before,item['before']);bind(after,item['after']);bind(P/'NLA/MI13'/f'{m}.lean',item['after'])
    a,b=before.read_text(),after.read_text()
    check('exact prefix cleanup diff '+m,''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),
          fromfile='before/'+m+'.lean',tofile='after/'+m+'.lean'))==item['diff'])
    old=code(a)
    if m=='Frobenius':old=old.replace('flatten, PiLp.toLp_apply, RCLike.inner_apply\'',"flatten, RCLike.inner_apply'").replace('simp [ite_mul, mul_comm]','simp [mul_comm]')
    check('only approved prefix comments/two unused args '+m,re.sub(r'\s+',' ',old)==re.sub(r'\s+',' ',code(b)))
for p in cleanup.iterdir():
    if p.is_file():copy(p,'evidence/cleanup/prefix/'+p.name)
for item in changes['quarantined_outputs'].values():bind(item['destination'],item['sha256'])
check('half certificate consumed twice by averaging',sources['NLA.MI13.ElementaryBounds'].count('half_certificate.1')==1
      and 'mul_le_mul_of_nonneg_left hsum hhalf' in sources['NLA.MI13.ElementaryBounds']
      and 'mul_nonneg hhalf (add_nonneg hx hy)' in sources['NLA.MI13.ElementaryBounds'])
check('one exact kernel interval tactic',sum(code(s).count('interval_decide') for s in sources.values())==1
      and 'interval_decide (trust := kernel)' in sources['NLA.MI13.Numerical'])

handoff_counts={}
for name in ['unitary-invariance-01','unitary-field-repair-01','commutator-maximum-01',
 'commutator-maximum-namespace-repair-01','spectral-maximum-simp-cleanup-01','two-unitary-average-01',
 'commutator-eigenspaces-01','cancelled-svd-01','refinedcommutator-01',
 'refined-cancellation-lemma-repair-01','refined-cancellation-lemma-repair-02',
 'norm-scaling-01','middlebounds-01','middle-zero-repair-01','sharpness-01','padding-01','padding-02',
 'padding-03','complete-01','operator-norm-comments-01','padding-simp-cleanup-01','circle-lemma-reuse-01']:
    d=P/'proof-handoffs'/name
    if (d/'MANIFEST.json').exists():handoff_counts[name]=manifest(d)
    else:
        fs=[p for p in d.rglob('*') if p.is_file()]
        for p in fs:bind(p)
        handoff_counts[name]={'bound_files_without_manifest':len(fs)}
    for p in d.iterdir():
        if p.is_file() and (p.suffix in ['.md','.diff','.patch','.json'] or p.name.endswith('.lean.txt')):
            copy(p,'evidence/handoffs/'+name+'/'+p.name)

provenance=read(P/'SOURCE-PROVENANCE.json');canonical=provenance['canonical']
bind(P/canonical['packet_path'],canonical['sha256'])
raw=(P/canonical['packet_path']).read_bytes()
check('literal canonical Git blob digest',hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==canonical['blob'])
for rel in ['SourceCorrespondence.md','NUMERICAL_TARGETS.md','NUMERICAL-FIRST.json','DEFINITION-AND-CONTRACT-PLAN.md',
 'SOURCE-PROVENANCE.json','REUSE-AUDIT.json','REVIEW-PLAN.md','sources/canonical/README.md','sources/route/FINITE-ROUTE.md',
 'formalization.yaml','README.md']:
    copy(P/rel,'evidence/context/'+rel)
reuse=read(P/'REUSE-AUDIT.json')
for item in reuse['standards']:
    bind(P/item['packet_path'],item['sha256']);copy(P/item['packet_path'],'evidence/standards/'+item['packet_path'].removeprefix('sources/standards/'))
environment=read(L/'LOCAL-ENVIRONMENT.json');compiler=environment['compiler']
bind(compiler,'1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554')
bind(L/'serial_compile_v3.py','d6c00e953688e155c0a313a8f49c7c395ad0fb1166faf3655c0b47f3ea2b2266')
copy(L/'serial_compile_v3.py','evidence/local/serial_compile_v3.py.txt')
copy(L/'LOCAL-ENVIRONMENT.json','evidence/local/LOCAL-ENVIRONMENT.json')
lock=read(P/'lake-manifest.json');shared=read(L/'lake-manifest.json')
pins={p['name']:p['rev'] for p in lock['packages']}
check('all ten shared package revisions identical',pins=={p['name']:p['rev'] for p in shared['packages']} and len(pins)==10)
check('all initial cache pins match',pins=={p['package']:p['commit'] for p in environment['dependencies']})
check('Lean4.33.1 exact shared toolchain',bind(L/'lean-toolchain')==sha(P/'lean-toolchain')
      and (P/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1')
for name,rev in pins.items():
    pkg=L/'.lake/packages'/name;head=pkg/'.git/HEAD';bind(head)
    value=head.read_text().strip()
    if value.startswith('ref: '):
        rf=pkg/'.git'/value.removeprefix('ref: ');bind(rf);value=rf.read_text().strip()
    check('literal installed package HEAD '+name,value==rev)
api_files={
 'Analysis/InnerProductSpace/Spectrum.lean','Analysis/InnerProductSpace/SingularValues.lean',
 'Analysis/InnerProductSpace/Adjoint.lean','Analysis/InnerProductSpace/PiL2.lean',
 'Analysis/InnerProductSpace/Rayleigh.lean','Analysis/Normed/Lp/Matrix.lean',
 'LinearAlgebra/Charpoly/ToMatrix.lean','LinearAlgebra/Matrix/Charpoly/Basic.lean',
 'LinearAlgebra/Matrix/Trace.lean','LinearAlgebra/Matrix/ConjTranspose.lean',
 'LinearAlgebra/Matrix/Reindex.lean','LinearAlgebra/Eigenspace/Basic.lean',
 'Data/Complex/Basic.lean','Data/Matrix/Diagonal.lean','Data/Matrix/Mul.lean','Data/Matrix/Block.lean',
 'Data/List/GetD.lean','Data/List/Sort.lean','Data/List/Pairwise.lean','Data/Multiset/Sort.lean',
 'Algebra/Polynomial/Roots.lean','Algebra/Module/LinearMap/Defs.lean',
 'Analysis/Complex/Norm.lean','Analysis/CStarAlgebra/Unitary/Span.lean','Algebra/Order/GroupWithZero/Defs.lean'}
primary={}
for rel in sorted(api_files):
    p=L/'.lake/packages/mathlib/Mathlib'/rel;primary['Mathlib/'+rel]=bind(p)
    copy(p,'evidence/primary/Mathlib/'+rel+'.txt')
for item in reuse['primary']:
    bind(item['source'],item['sha256']);bind(P/item['packet_path'],item['sha256'])
write('PRIMARY-BINDINGS.json',{'pinned_mathlib':pins['mathlib'],'files':primary,
 'reading_scope':'Selected source APIs and surrounding proofs; complete files retained for binding, not a claim to have read every complete library file.',
 'reuse_search_scope':'Recorded targeted rg searches, not global absence of equivalent theorems or fresh network audit.'})

receipts,assemblies={},{}
def loadrun(k):
    if k in receipts:return receipts[k]
    rp=L/f'runs/development-{k:02d}/RECEIPT.json';ap=L/f'ASSEMBLY-{k:02d}.json'
    r,a=read(rp),read(ap);receipts[k]=r;assemblies[k]=a
    check('assembly equality '+str(k),r['assembly_sha256']==sha(ap)
        and r['source_inputs']=={rel:v['sha256'] for rel,v in a['sources'].items()})
    check('actual resources '+str(k),(r['platform'],r['max_compiler_processes'],r['threads'],r['memory_cap_mib'])==('darwin',1,1,4096))
    check('actual pinned compiler/runner '+str(k),r['compiler_sha256']==sha(compiler)
        and r['runner_sha256']==sha(L/'serial_compile_v3.py'))
    copy(rp,f'evidence/local/development-{k:02d}/RECEIPT.json');copy(ap,f'evidence/local/ASSEMBLY-{k:02d}.json')
    return r
traces,visiting={},set()
def trace(k,m):
    key=(k,m)
    if key in traces:return traces[key]
    check('acyclic output reuse '+str(key),key not in visiting);visiting.add(key)
    r=loadrun(k);c=next(c for c in r['commands'] if c['module']==m)
    check('exact source closure '+str(key),c['source_sha256']==expected[m]
        and all(r['source_inputs'][relative[d]]==expected[d] for d in closure(m)))
    out=L/'.lake/build/lib/lean'/relative[m].replace('.lean','.olean');bind(out,c['output_sha256'])
    if c.get('status')=='reused_exact_successful_local_output':
        prior=Path(c['prior_receipt']);bind(prior,c['prior_receipt_sha256']);oldk=int(prior.parent.name.removeprefix('development-'))
        oldr=loadrun(oldk)
        check('earlier completed receipt '+str(key),oldk<k and oldr['end']<=r['start'])
        check('exact transitive source reuse '+str(key),c['transitive_source_hashes']=={relative[d]:expected[d] for d in closure(m)})
        oldc=next(x for x in oldr['commands'] if x['module']==m)
        check('identical successful prior output '+str(key),oldc['output_sha256']==c['output_sha256'])
        priortrace=trace(oldk,m);value={'run':k,'module':m,'origin_run':priortrace['origin_run'],'chain':[k]+priortrace['chain']}
    else:
        check('actual successful origin '+str(key),c['exit_code']==0)
        check('literal command '+str(key),c['argv']==[compiler,'--threads=1','--memory=4096','-o',str(out),relative[m]] and c['cwd']==str(L))
        check('actual time ordering '+str(key),r['start']<=c['start']<=c['end']<=r['end'])
        check('immediate output dependencies '+str(key),set(c['dependency_olean_sha256'])==set(imports[m]))
        for dep,h in c['dependency_olean_sha256'].items():
            earlier=[x for x in r['commands'][:r['commands'].index(c)] if x['module']==dep]
            check('earlier dependency output '+str((key,dep)),len(earlier)==1 and earlier[0]['output_sha256']==h)
            trace(k,dep)
        log=L/f'runs/development-{k:02d}'/(m+'.log');bind(log,c['log_sha256']);copy(log,f'evidence/local/development-{k:02d}/'+log.name)
        content=log.read_text();got=re.findall(r"^'NLA\.MI13\.(\w+)' depends on axioms: \[([^\]]*)\]$",content,re.M)
        check('exact origin axiom exports '+str(key),[name for name,_ in got]==assertions[m])
        check('standard three axioms only '+str(key),all(ax=='propext, Classical.choice, Quot.sound' for _,ax in got))
        check('clean final source origin log '+str(key),not re.search(r'warning:|error:|sorryAx|ofReduceBool',content))
        value={'run':k,'module':m,'origin_run':k,'chain':[k]}
    value['source_sha256']=expected[m];value['output_sha256']=c['output_sha256']
    visiting.remove(key);traces[key]=value;return value
final=loadrun(run)
scoped_commands=[c for c in final['commands'] if c['module'] in expected]
outside_commands=[c['module'] for c in final['commands'] if c['module'] not in expected]
check('all22 MI13 modules selected and completed',set(c['module'] for c in scoped_commands)==set(expected)
      and len(scoped_commands)==22 and final['failed_modules']==[] and final['blocked_modules']==[]
      and final['completed_modules']==len(final['commands'])==len(final['module_order']))
check('only separately scoped IE02 additions to final serial run',outside_commands==['NLA.IE02.Definitions','NLA.IE02.Coefficients'])
for m in expected:trace(run,m)
for m in expected:copy(L/'.lake/build/lib/lean'/relative[m].replace('.lean','.olean'),'evidence/outputs/'+relative[m].replace('.lean','.olean'))
check('Numerical actual run follows root acceptance',acceptance['time_utc']<=loadrun(21)['start'])
historical=[]
for k in [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,36,37,38,39,40,41,43,44,45,46,47,48,49,51,52]:
    r=loadrun(k)
    for p in sorted((L/f'runs/development-{k:02d}').glob('*.log')):
        if p.name.startswith('NLA.MI13.') or p.name=='Solution.log':
            c=next(c for c in r['commands'] if c['module']==p.name[:-4]);bind(p,c['log_sha256'])
            copy(p,f'evidence/local/development-{k:02d}/'+p.name)
    historical.append({'run':k,'receipt_sha256':sha(L/f'runs/development-{k:02d}/RECEIPT.json'),
        'failed':r['failed_modules'],'blocked':r['blocked_modules']})
check('failed49 retained without Complete/Solution acceptance',loadrun(49)['failed_modules']==['NLA.MI13.Padding']
      and loadrun(49)['blocked_modules']==['NLA.MI13.Complete','Solution'])
check('standard-four scoped final origins',traces[(run,'NLA.MI13.UnitaryInvariance')]['origin_run']==40
      and traces[(run,'NLA.MI13.CommutatorMaximum')]['origin_run']==41
      and traces[(run,'NLA.MI13.TwoUnitaryAverage')]['origin_run']==run)
write('REUSE-CHAINS.json',list(traces.values()))
write('RUNTIME.json',{'scope':'Authentication and reading of retained macOS evidence; no execution by this reviewer.',
    'final_run':run,'receipt_sha256':sha(L/f'runs/development-{run:02d}/RECEIPT.json'),
    'assembly_sha256':sha(L/f'ASSEMBLY-{run:02d}.json'),'final_MI13_commands':scoped_commands,'historical':historical,
    'total_final_serial_module_count':len(final['commands']),'outside_proof_review_scope_modules':outside_commands,
    'fresh_final_MI13_modules':[c['module'] for c in scoped_commands if c.get('status')!='reused_exact_successful_local_output'],
    'current_origins':{m:traces[(run,m)]['origin_run'] for m in expected},
    'GitHub_Comparator_kernel_replay_sandbox_controls_executed_here':False})
for path,h in list(bindings.items()):check('final input stable '+path,sha(path)==h)
write('BINDINGS.json',bindings);write('CHECKS.json',checks)
result={'reviewer':'/root/sf_ra_runtime_referee','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'automated_evidence_verdict':'PASS','mathematical_verdict':'See independently authored REVIEW.md, not inferred from this script.',
 'scope':'All22 implementation inputs,36 unchanged frozen contracts, exact successful local source/output closure.',
 'checks':len(checks),'external_bindings':len(bindings),'implementation_inputs':len(current),'contracts':len(headers),
 'frozen_inputs':13,'prior_own_review_payload_counts':prior_counts,'handoff_payload_counts':handoff_counts,
 'runtime_nodes':len(traces),'final_actual_local_run':run,'reviewer_invoked_compiler':False,
 'GitHub_Comparator_or_publication_approval':False,'count_change':0}
write('AUDIT.json',result);print(json.dumps(result,indent=2))

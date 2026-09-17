#!/usr/bin/env python3
"""Authenticate retained local evidence only. Never invoke a compiler or network."""
from pathlib import Path
import hashlib,json,re,sys,datetime
R=Path(__file__).resolve().parent
P=Path('/tmp/nla-lean-next-20260915/next-proofs/MI-13').resolve()
L=Path('/private/tmp/nla-lean-local-shared-20260916')
root_receipt=Path(sys.argv[1]).resolve()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
checks=[];bindings={};nodes={};actuals={};receipts={}
def check(label,ok):
 checks.append({'label':label,'pass':bool(ok)})
 if not ok:raise AssertionError(label)
def bind(p,expected=None):
 p=Path(p).resolve();h=sha(p)
 if expected:check('sha '+str(p),h==expected)
 bindings[str(p)]=h
 return h
files=sorted(P.glob('NLA/MI13/*.lean'))+[P/'Solution.lean']
mods={str(p.relative_to(P))[:-5].replace('/','.'):p for p in files}
imports={m:[d for d in re.findall(r'^import (\S+)$',p.read_text(),re.M) if d.startswith('NLA.')] for m,p in mods.items()}
closures={}
def closure(m):
 if m not in closures:
  ds={m}
  for d in imports[m]:ds|=closure(d)
  closures[m]=ds
 return closures[m]
closure('Solution')
check('all project inputs in Solution closure',closures['Solution']==set(mods))
for m,p in mods.items():
 bind(p);rel=p.relative_to(P)
 check('current shared input '+m,sha(L/rel)==sha(p));bind(L/rel)
def get_receipt(p):
 p=Path(p).resolve()
 if p not in receipts:
  bind(p);j=json.loads(p.read_text());receipts[p]=j
  check('ended '+str(p),'end' in j)
  check('one process thread 4096 '+str(p),j['max_compiler_processes']==1 and j['threads']==1 and j['memory_cap_mib']==4096)
  check('Darwin local scope '+str(p),j['platform']=='darwin')
  n=p.parent.name.removeprefix('development-')
  bind(L/('ASSEMBLY-'+n+'.json'),j['assembly_sha256'])
  runner=[q for q in L.glob('serial_compile*.py') if sha(q)==j['runner_sha256']]
  check('retained runner '+str(p),len(runner)>0);bind(runner[0],j['runner_sha256'])
  env=json.loads((L/'LOCAL-ENVIRONMENT.json').read_text());bind(L/'LOCAL-ENVIRONMENT.json')
  bind(env['compiler'],j['compiler_sha256'])
 return receipts[p]
def audit(p,m,expected_output=None):
 p=Path(p).resolve();key=(str(p),m)
 if key in nodes:
  if expected_output:check('cached output equality '+str(key),nodes[key]['output_sha256']==expected_output)
  return nodes[key]
 j=get_receipt(p);cs=[c for c in j['commands'] if c['module']==m]
 check('unique command '+str(key),len(cs)==1);c=cs[0]
 check('module input '+str(key),c.get('source_sha256')==sha(mods[m]))
 if expected_output:check('output chain '+str(key),c.get('output_sha256')==expected_output)
 for d in closure(m):
  rel=str(mods[d].relative_to(P));v=j['source_inputs'].get(rel)
  if isinstance(v,dict):v=v['sha256']
  check('transitive source '+str(key)+' '+d,v==sha(mods[d]))
 if c.get('status')=='reused_exact_successful_local_output':
  pp=Path(c['prior_receipt']).resolve();bind(pp,c['prior_receipt_sha256'])
  declared=c['transitive_source_hashes']
  check('exact reuse closure '+str(key),set(declared)=={str(mods[d].relative_to(P)) for d in closure(m)})
  for rel,h in declared.items():check('reuse closure hash '+str(key)+' '+rel,sha(P/rel)==h)
  actual=audit(pp,m,c['output_sha256'])
 else:
  check('actual exit zero '+str(key),c.get('exit_code')==0)
  argv=c['argv'];check('actual resource flags '+str(key),'--threads=1' in argv and '--memory=4096' in argv)
  check('actual correct input '+str(key),argv[-1]==str(mods[m].relative_to(P)))
  check('actual working dir '+str(key),Path(c['cwd']).resolve()==L)
  log=p.parent/(m+'.log');bind(log,c['log_sha256']);text=log.read_text()
  check('actual no sorry/error warning '+str(key),not re.search(r'uses .sorry.|\berror:',text))
  check('actual elapsed ≤ 180s '+str(key),0<=c['elapsed_seconds']<180)
  for d,h in c['dependency_olean_sha256'].items():
   check('direct dependency belongs '+str(key)+' '+d,d in imports[m])
   audit(p,d,h)
  actual={'actual_receipt':str(p),'actual_module':m,'source_sha256':c['source_sha256'],'output_sha256':c['output_sha256'],'log':str(log),'log_sha256':c['log_sha256'],'elapsed_seconds':c['elapsed_seconds']}
  actuals[m]=actual
 nodes[key]=actual
 return actual
j=get_receipt(root_receipt)
check('full final local success',j['failed_modules']==[] and j['blocked_modules']==[])
selected=[m for m in j['module_order'] if m=='Solution' or m.startswith('NLA.MI13.')]
excluded=[m for m in j['module_order'] if m not in selected]
check('exact MI13 module order set',set(selected)==set(mods) and len(selected)==len(mods))
for m in mods:
 a=audit(root_receipt,m)
 out=L/'.lake/build/lib/lean'/str(mods[m].relative_to(P)).replace('.lean','.olean')
 bind(out,a['output_sha256'])
solution_actual=actuals['Solution'];log=Path(solution_actual['log']).read_text()
measured={name:set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',axioms)) for name,axioms in re.findall(r"'(NLA\.MI13\.[^']+)' depends on axioms: \[([^\]]*)\]",log)}
contracts=json.loads((P/'comparator.json').read_text())['theorem_names']
check('36 actual Solution axiom reports',set(measured)==set(contracts))
for name,axioms in measured.items():check('permitted measured axioms '+name,axioms<={'propext','Classical.choice','Quot.sound'})
# Copy retained evidence into this independent read-only report package.
for p in receipts:
 dest=R/'runtime'/p.parent.name/'RECEIPT.json';dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
 n=p.parent.name.removeprefix('development-');q=L/('ASSEMBLY-'+n+'.json');(dest.parent/q.name).write_bytes(q.read_bytes())
for a in actuals.values():
 p=Path(a['log']);dest=R/'runtime'/p.parent.name/p.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
result={'scope':'Independent authentication of root-executed retained macOS local Lean receipts. This agent did not invoke Lean, Lake, Git, network, Comparator or a sandbox. Not a fresh independent execution and not publication verification.','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_receipt':str(root_receipt),'root_receipt_sha256':sha(root_receipt),'excluded_unrelated_modules':excluded,'actual_module_executions':actuals,'runtime_chain_nodes':len(nodes),'receipt_count':len(receipts),'checks':checks,'check_count':len(checks),'bindings':bindings,'measured_axioms':{n:sorted(v) for n,v in measured.items()},'all_passed':True,'fresh_compilation_by_referee':False,'Comparator_executed':False,'published_commit_checked':False,'count_change':0}
print(json.dumps(result,indent=2))

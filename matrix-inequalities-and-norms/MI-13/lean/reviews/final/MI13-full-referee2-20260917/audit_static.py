#!/usr/bin/env python3
"""Read-only project audit; never invokes Lean, Lake, Git, network or Comparator."""
from pathlib import Path
import hashlib,json,re,sys,datetime
R=Path(__file__).resolve().parent
P=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else R/'baseline45'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
checks=[]
def check(label,ok):
 checks.append({'label':label,'pass':bool(ok)})
 if not ok: raise AssertionError(label)
def uncomments(s):
 out=[];i=0;level=0
 while i<len(s):
  if s[i:i+2]=='/-':level+=1;i+=2;continue
  if level and s[i:i+2]=='-/':level-=1;i+=2;continue
  if not level and s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j;continue
  out.append(s[i] if level==0 or s[i]=='\n' else ' ');i+=1
 return ''.join(out)
freeze=json.loads((P/'STATEMENT-FREEZE.json').read_text())
for rel,h in freeze['frozen_files'].items():
 check('freeze '+rel,sha(P/rel)==h)
headers=json.loads((P/'STATEMENT-HEADERS.json').read_text())['declarations']
check('36 frozen headers',len(headers)==36)
proofs=sorted(P.glob('NLA/MI13/*.lean'))+[P/'Solution.lean']
impl={str(p.relative_to(P)):p.read_text() for p in proofs}
code={p:uncomments(t) for p,t in impl.items()}
check('22 active inputs at first full candidate',len(impl)==22)
for rel,s in code.items():
 for pattern in [r'\bsorry\b',r'\badmit\b',r'^\s*axiom\b',r'\bnative_decide\b',r'\bunsafe\b',r'^\s*#eval\b',r'^\s*run_elab\b',r'\bimplemented_by\b',r'^\s*variable\b']:
  check('no forbidden '+pattern+' '+rel,re.search(pattern,s,re.M) is None)
 check('no Challenge import '+rel,re.search(r'^import .*\bChallenge\b',s,re.M) is None)
 check('explicit autoImplicit false '+rel,'set_option autoImplicit false' in s)
 check('namespace restricted '+rel,set(re.findall(r'^namespace (.+)$',s,re.M))=={'NLA.MI13'})
rows=[]
for row in headers:
 short=row['name'].split('.')[-1]; hits=[]
 for rel,s in code.items():
  m=re.search(r'^theorem '+re.escape(short)+r'(?=\s|\{).*?(?=\s*:=\s*by\b)',s,re.M|re.S)
  if m:hits.append((rel,m.group().strip()))
 check('unique implementation '+short,len(hits)==1)
 rel,header=hits[0]
 check('exact frozen header '+short,header==row['header'])
 check('header hash '+short,hashlib.sha256(header.encode()).hexdigest()==row['header_sha256'])
 rows.append({'name':row['name'],'implementation':rel,'header_sha256':row['header_sha256'],'source_sha256':sha(P/rel)})
config=json.loads((P/'comparator.json').read_text())
check('Comparator exact ordered contract set',config['theorem_names']==[r['name'] for r in headers])
check('Comparator no definition holes',config['definition_names']==[])
check('Comparator standard axioms only',set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
check('Challenge only concrete Definitions import',re.findall(r'^import (.+)$',(P/'Challenge.lean').read_text(),re.M)==['NLA.MI13.Definitions'])
check('36 deliberate Challenge holes',len(re.findall(r'\bsorry\b',uncomments((P/'Challenge.lean').read_text())))==36)
modules={rel[:-5].replace('/','.'):(rel,s) for rel,s in code.items()}
seen=set()
def visit(m):
 if m in seen:return
 check('closed project module '+m,m in modules)
 seen.add(m)
 for dep in re.findall(r'^import (\S+)$',modules[m][1],re.M):
  if dep.startswith('NLA.'):visit(dep)
visit('Solution')
check('Solution actual whole implementation closure',seen==set(modules))
num=code['NLA/MI13/Numerical.lean'];elem=code['NLA/MI13/ElementaryBounds.lean']
check('single exact kernel interval_decide',sum(s.count('interval_decide') for s in code.values())==1 and 'interval_decide (trust := kernel)' in num)
check('positive half genuinely referenced by averaging','have hhalf : (0 : ℝ) ≤ 1 / 2 := le_of_lt half_certificate.1' in elem and 'mul_le_mul_of_nonneg_left hsum hhalf' in elem)
solution=code['Solution.lean']
check('all 36 standard axiom print requests',re.findall(r'^#print axioms (\w+)$',solution,re.M)==[r['name'].split('.')[-1] for r in headers])
check('all 36 kernel trust assertions',re.findall(r'^#assert_trust kernel (\w+)$',solution,re.M)==[r['name'].split('.')[-1] for r in headers])
check('author and department university',all('George Stepaniants' in s and 'Department of Computing and Mathematical Sciences, California Institute of Technology.' in s for s in impl.values()))
check('no author email in active sources',not any(re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',s) for s in impl.values()))
result={'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Independent static and textual-contract audit only; no elaboration, Comparator, kernel rerun or publication verification. Exact reviewed compiled source and runtime receipts are separate gates.','project':str(P),'files':{rel:sha(P/rel) for rel in impl},'source_lines':sum(len(s.splitlines()) for s in impl.values()),'contracts':rows,'checks':checks,'check_count':len(checks),'successful':True,'compiler_invoked':False,'Comparator_invoked':False,'count_change':0}
print(json.dumps(result,indent=2))

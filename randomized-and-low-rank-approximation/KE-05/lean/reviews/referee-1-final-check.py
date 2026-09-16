from pathlib import Path
import hashlib,json,re,subprocess
from fractions import Fraction as F
p=Path(__file__).resolve().parents[1]; root=p.parents[2]
def sha(b): return hashlib.sha256(b).hexdigest()
def h(path): return sha((p/path).read_bytes())
receipt=json.loads((p/'verification/local-proof.json').read_text())
freeze=json.loads((p/'verification/statement-freeze.json').read_text())
for group in ['file_sha256','log_sha256']:
 for path,expected in receipt[group].items(): assert h(path)==expected,(path,'stale receipt')
rev=json.loads((p/'verification/build-config-revision.json').read_text())
old=(p/rev['old_bytes']).read_bytes(); new=(p/'lakefile.toml').read_bytes()
assert sha(old)==rev['before_sha256'] and sha(new)==rev['after_sha256']
assert new==old+rev['exact_added_text'].encode()
for path,expected in freeze['files_sha256'].items():
 assert (sha(old) if path=='lakefile.toml' else h(path))==expected,path
for path,expected in freeze['referees'].items(): assert h(path)==expected,path
sources=[]
for item in freeze['sources']:
 path=item['repository_path']; data=(root/path).read_bytes()
 assert sha(data)==item['sha256']
 for base in [freeze['source_base'],'deb549fa9ddd6b119e6c59016f268237e645dfa2']:
  assert subprocess.check_output(['git','show',base+':'+path],cwd=root)==data
 sources.append({'path':path,'sha256':sha(data)})
active=sorted(p.glob('NLA/KE05/*.lean'))+[p/'Solution.lean']
assert len(active)==22
for file in active:
 text=re.sub(r'/\-.*?\-/','',file.read_text(),flags=re.S)
 assert not re.search(r'\b(sorry|axiom|native_decide|admit)\b|import Challenge',text),file
 for module in re.findall(r'^import (NLA\.KE05\.[\w]+)',text,re.M): assert p.joinpath(*module.split('.')).with_suffix('.lean') in active
exports=receipt['exports']; consumer=(p/'reviews/referee-1-final-consumer.log').read_text()
assert len(exports)==10 and 'error:' not in consumer
for n in exports: assert "'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in consumer,n
assert 'Build completed successfully (8730 jobs).' in (p/receipt['build_log']).read_text()
# Fresh exact arithmetic is a diagnostic, distinct from the proof and norm theorem.
def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def sub(a,b):return [[a[i][j]-b[i][j] for j in range(2)] for i in range(2)]
def inv(a):
 d=a[0][0]*a[1][1]-a[0][1]*a[1][0]
 return [[a[1][1]/d,-a[0][1]/d],[-a[1][0]/d,a[0][0]/d]]
I=[[F(1),F(0)],[F(0),F(1)]]; O=[[F(1),F(2)],[F(3),F(5)]]
X=[[F(1),F(0)],[F(0),F(2)]]; P=mm(mm(inv(O),[[F(0),F(0)],[F(0),F(1)]]),O)
Q=mm(mm(sub(I,P),X),P); K=mm(sub(I,P),X); k=K[0][0]+K[1][1]
assert P==[[6,10],[-3,-5]] and Q==[[30,50],[-18,-30]] and k==7
assert F(34)*F(136,49)==F(68,7)**2
libraries=['.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Matrix.lean','.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean','.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Indicator.lean','.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean','.lake/packages/LeanCert/LeanCert/Tactic/Verification.lean']
attachments=['verification/local-proof.json','verification/statement-freeze.json','verification/build-config-revision.json','reviews/proof-source-hashes.json','reviews/referee-1-final-consumer.lean','reviews/referee-1-final-consumer.log','reviews/referee-1-final-check.py']+list(receipt['log_sha256'])
evidence={'verdict':'PASS','reviewer':'/root/iv06_statement_referee_1; independent nonauthor AI reviewer','head_at_review':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'scope':'complete KE-05 negative target; local audit only, Linux Comparator separate','active_closure':[{'path':str(f.relative_to(p)),'sha256':sha(f.read_bytes())} for f in active],'boundary_hashes':{k:h(k) for k in freeze['files_sha256']},'source_hashes':sources,'library_hashes':{k:h(k) for k in libraries},'evidence_hashes':{k:h(k) for k in attachments},'consumer_exit_code':0,'consumer_command':'PATH=/private/tmp/nla-lean-runtime/lean-4.33.1-darwin_aarch64/bin:$PATH lake env lean reviews/referee-1-final-consumer.lean','consumer_scope':'fresh referee execution; ten frozen Challenge signatures applied to actual Solution exports, ten kernel trust assertions and axiom queries','full_build_provenance':'author/coordinator execution inspected and hash-verified; no duplicate full build by this referee','exact_diagnostic':'Fraction arithmetic verifies P,Q,kappa and rank-one norm squared identity; not a proof substitute','leanCert_role':'actual kernel axiom audits only; exact algebra requires no interval numerical certificate','read_documents':{k:h(k) for k in ['README.md','PROOF_NOTES.md','NUMERICAL_TARGETS.md','Challenge.lean','formalization.yaml','comparator.json','SOURCE_PROVENANCE.json']},'build_only_change':'exact appended Solution library registration verified against retained frozen old bytes'}
(p/'reviews/referee-1-final-evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
print('PASS: 22 active modules; 10 exact-signature consumers and standard-three closures; all local source/log hashes; all frozen boundaries except explicitly verified additive Solution registration; original canonical and complete source equal both preserved bases; exact rational diagnostic.')

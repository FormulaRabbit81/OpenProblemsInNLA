from pathlib import Path
import hashlib,json,subprocess,os,datetime
p=Path(__file__).resolve().parent.parent
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
local=json.loads((p/'verification/local-proof.json').read_text())
freeze=json.loads((p/'statement-freeze.json').read_text())
checks={str(f):sha(p/f)==v for f,v in {**local['file_sha256'],**local['log_sha256'],**freeze['sha256']}.items()}
assert all(checks.values()),checks
names=json.loads((p/'comparator.json').read_text())['theorem_names']
c=p/'reviews/referee-2-final-consumer.lean'
c.write_text('import Solution\nset_option pp.universes true\n'+''.join(f'#check {n}\n#print axioms {n}\n#assert_trust kernel {n}\n' for n in names))
env=os.environ.copy();env['PATH']='/private/tmp/nla-lean-runtime/lean-4.33.1-darwin_aarch64/bin:'+env['PATH']
cmd=['lake','env','lean',str(c)]
r=subprocess.run(cmd,cwd=p,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
log=p/'reviews/referee-2-final-consumer.log';log.write_text(r.stdout)
inputs=list(local['file_sha256'])+list(local['log_sha256'])+['statement-freeze.json','SOURCE_PROVENANCE.json','reviews/referee-2-final-consumer.lean']
source=json.loads((p/'SOURCE_PROVENANCE.json').read_text());root=p.parents[2]
for d in source['sources']:
 f=root/d['path'];assert sha(f)==d['sha256'];inputs.append(str(f))
for f in ['LinearAlgebra/Matrix/NonsingularInverse.lean','LinearAlgebra/Matrix/Adjugate.lean','LinearAlgebra/Matrix/Rank.lean','LinearAlgebra/Matrix/SchurComplement.lean','Topology/Order/IntermediateValue.lean']:
 inputs.append(str(p/'.lake/packages/mathlib/Mathlib'/f))
e={'phase':'independent final proof review','reviewer':'/root/iv06_statement_referee_2','ai_agent':True,'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':cmd,'consumer_exit_code':r.returncode,'export_count':len(names),'export_names':names,'frozen_and_local_receipt_hash_checks':checks,'input_sha256':{f:sha(p/f) for f in inputs},'consumer_log_sha256':sha(log),'limitations':['Linux Comparator not yet inspected or claimed','Coordinator local build was inspected; this consumer is independently executed']}
(p/'reviews/referee-2-final-evidence.json').write_text(json.dumps(e,indent=2)+'\n')
print(json.dumps({'consumer_exit_code':r.returncode,'hash_checks':len(checks),'export_count':len(names)},indent=2))
raise SystemExit(r.returncode)

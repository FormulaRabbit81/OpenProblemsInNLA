#!/usr/bin/env python3
"""Read-only integrity and pre-code inventory verifier; does not run Lean or prove mathematics."""
from pathlib import Path
import json,hashlib,sys
p=Path(__file__).resolve().parent
m=json.loads((p/'MANIFEST.json').read_text()); checks=0
expected=set()
for row in m['files']:
 q=p/row['path']; assert q.is_file(),str(q)
 b=q.read_bytes(); assert len(b)==row['bytes'],row['path']
 assert hashlib.sha256(b).hexdigest()==row['sha256'],row['path']
 expected.add(row['path']); checks+=3
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file()}
assert actual-{'MANIFEST.json','VERIFICATION.json'}==expected; checks+=1
s=json.loads((p/'SOURCE-BINDINGS.json').read_text())
for row in s['records']:
 b=(p/row['path']).read_bytes()
 assert len(b)==row['bytes']; assert hashlib.sha256(b).hexdigest()==row['sha256']; checks+=2
c=json.loads((p/'CONTRACT-PLAN.json').read_text())
assert c['theorem_count']==35==len(c['contracts']); checks+=1
assert len({r['name'] for r in c['contracts']})==35; checks+=1
assert all(r['status']=='planned_not_written_not_typechecked' for r in c['contracts']); checks+=1
assert c['definition_holes']==[]; checks+=1
assert c['contracts'][-1]['name']=='NLA.NM04.rowland_wu_identity'; checks+=1
assert c['permitted_axioms']==['propext','Quot.sound','Classical.choice']; checks+=1
assert not list(p.rglob('*.lean')); checks+=1
assert not list(p.rglob('*.olean')); checks+=1
assert not list(p.rglob('lakefile.*')); checks+=1
assert not list(p.rglob('Solution.*')); checks+=1
assert (p/'sources/canonical/NM-04_sinkhorn_identity.tex.txt').read_bytes().count(b'\\label{thm:main}')==1; checks+=1
assert hashlib.sha256((p/'sources/triage/MANIFEST.json').read_bytes()).hexdigest()=='cc93974726a4b7b51d9a6360175819a4cfb306203e5b389d3a49f2dbea198d3f'; checks+=1
r=json.loads((p/'READ-AND-STATUS.json').read_text())
assert r['review_gate']['accepted']==0; checks+=1
print(json.dumps({'status':'PASS_PRECODE_PACKET_INTEGRITY_ONLY','checks':checks,'payloads':len(expected),'source_copies':len(s['records']),'contracts':35,'lean_executed':False,'leancert_executed':False,'comparator_executed':False,'independent_review_acceptances_claimed':0,'mathematical_correctness_certified_by_this_script':False,'manifest_sha256':hashlib.sha256((p/'MANIFEST.json').read_bytes()).hexdigest()},indent=2))

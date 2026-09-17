from pathlib import Path
import hashlib,json,re,datetime
p=Path(__file__).resolve().parent.parent
sha=lambda f:hashlib.sha256((p/f).read_bytes()).hexdigest()
freeze=json.loads((p/'verification/statement-freeze.json').read_text())
checks={f:sha(f)==v for f,v in freeze['files_sha256'].items()}
assert all(ok for f,ok in checks.items() if f!='lakefile.toml')
rev=json.loads((p/'verification/build-config-revision.json').read_text())
assert sha('lakefile.toml')==rev['after_sha256'] and sha(rev['old_bytes'])==freeze['files_sha256']['lakefile.toml']
assert (p/'lakefile.toml').read_bytes()==(p/rev['old_bytes']).read_bytes()+rev['exact_added_text'].encode()
files=[str(f.relative_to(p)) for f in sorted((p/'NLA/KE05').glob('*.lean'))]+['Solution.lean','Challenge.lean','NUMERICAL_TARGETS.md','comparator.json','formalization.yaml','README.md','PROOF_NOTES.md','lakefile.toml','lake-manifest.json','lean-toolchain','SOURCE_PROVENANCE.json','verification/build-config-revision.json']
logs=['verification/local-solution-build.log','verification/solution-direct.log','verification/manifest-validation.log']
build=(p/logs[0]).read_text();m=re.search(r'Build completed successfully \((\d+) jobs\)',build);assert m
names=json.loads((p/'comparator.json').read_text())['theorem_names']
for name in names:
 for f in logs[:2]:assert f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in (p/f).read_text()
assert 'error:' not in build and 'error:' not in (p/logs[1]).read_text()
r={'stage':'complete local proof; independent final reviews and Linux Comparator pending','created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'build_exit':0,'build_jobs':int(m[1]),'build_command':'lake build Solution','build_log':logs[0],'direct_export_audit_exit':0,'direct_export_audit_command':'lake env lean Solution.lean','direct_export_audit_log':logs[1],'exports':names,'axioms':['propext','Classical.choice','Quot.sound'],'frozen_bytes_unchanged':checks,'build_only_exception':'lakefile.toml adds only the Solution library; exact old bytes and additive diff retained in verification/build-config-revision.json','file_sha256':{f:sha(f) for f in files},'log_sha256':{f:sha(f) for f in logs},'not_yet_claimed':['independent final code approvals','isolated Linux Comparator and rejection controls','canonical Lean-verified publication status']}
(p/'verification/local-proof.json').write_text(json.dumps(r,indent=2)+'\n')
(p/'reviews/proof-source-hashes.json').write_text(json.dumps({'phase':r['stage'],'files_sha256':r['file_sha256'],'log_sha256':r['log_sha256']},indent=2)+'\n')
print(json.dumps({'build_jobs':r['build_jobs'],'exports':len(names),'all_math_and_pins_unchanged':all(ok for f,ok in checks.items() if f!='lakefile.toml'),'receipt_sha256':sha('verification/local-proof.json')},indent=2))

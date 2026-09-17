import hashlib, json, pathlib, subprocess
project=pathlib.Path(__file__).resolve().parent.parent
root=project.parents[2]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def gitbytes(ref,p): return subprocess.check_output(['git','show',ref+':'+p],cwd=root)
receipt=json.loads((project/'verification/local-proof.json').read_text())
for name,want in receipt['file_sha256'].items():
    assert sha(project/name)==want,(name,'changed since local proof receipt')
for name,want in receipt['log_sha256'].items():
    assert sha(project/name)==want,(name,'changed log')
freeze=json.loads((project/'statement-freeze.json').read_text())
for name,want in freeze['sha256'].items():assert sha(project/name)==want,name
active=sorted(project.glob('NLA/IV03/*.lean'))+[project/'Solution.lean']
for p in active:
    s=p.read_text()
    assert not any(x in s for x in ['import Challenge','by sorry','sorryAx','native_decide','axiom ']),p
source_paths=['intervals-and-absolute-value-equations/IV-03/README.md','references/colbrook-intervals-2026-09-11/manuscripts/IV-03.tex']
sources={}
for p in source_paths:
    b=(root/p).read_bytes()
    assert b==gitbytes('deb549fa9ddd6b119e6c59016f268237e645dfa2',p),p
    assert b==gitbytes('32f1f799219fbcaf4c66bfaa4edb8a0c591e79e9',p),p
    sources[p]=hashlib.sha256(b).hexdigest()
log=(project/'reviews/referee-1-final-consumer.log').read_text()
for name in ['vertex_formula','vertices_admissible','nSquaredCriterion','twoSignCriterion']:
    assert f"'NLA.IV03.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
assert 'error:' not in log
lib=['.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/'+x+'.lean' for x in ['NonsingularInverse','Adjugate','Rank','SchurComplement']]+['.lake/packages/leancert/LeanCert/Tactic/Verification.lean']
evidence={
 'reviewer':'/root/iv06_statement_referee_1','ai_agent':True,'nonauthor_of_IV03':True,'phase':'final source and proof review','verdict':'PASS',
 'checkout_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
 'reviewed_revision':'working-tree candidate bound by exact SHA-256 values; not a claim that uncommitted proof files belong to HEAD',
 'active_closure':{str(p.relative_to(project)):sha(p) for p in active},
 'boundary_hashes':freeze['sha256'],'original_sources':sources,
 'metadata_and_notes':{x:sha(project/x) for x in ['formalization.yaml','PROOF_NOTES.md','SOURCE_PROVENANCE.json','statement-freeze.json','verification/local-proof.json']},
 'library_sources_inspected':{x:sha(project/x) for x in lib},
 'execution':{'independent_consumer_exit_code':0,'command':'PATH=/private/tmp/nla-lean-runtime/lean-4.33.1-darwin_aarch64/bin:$PATH lake env lean reviews/referee-1-final-consumer.lean','exports':4,'all_export_axioms':['propext','Classical.choice','Quot.sound'],'author_build':'inspected actual local-solution-build.log: PASS 8804; not executed by this referee','Linux Comparator':'pending; not executed or inferred'},
 'evidence_hashes':{x:sha(project/x) for x in ['reviews/referee-1-final-consumer.lean','reviews/referee-1-final-consumer.log','reviews/referee-1-final-check.py','verification/local-solution-build.log','verification/solution-direct.log','verification/manifest-validation.log']},
 'checks':{'all_receipt_source_and_log_hashes_match':True,'all_frozen_boundary_hashes_match':True,'all_original_source_bytes_match_both_recorded_commits':True,'all_13_active_sources_read':True,'all_four_frozen_export_types_consumed_independently':True},
 'limits':['No Linux Comparator or sandbox/rejection-control result claimed.','No human or official Tau Ceti review claimed.','LeanCert is used for kernel trust audits; this symbolic proof uses no numerical interval certificate.','A polynomial arithmetic-operation or bit-complexity theorem is not formalized.']}
(project/'reviews/referee-1-final-evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
print('PASS: original sources, all 13 active sources, all frozen bytes, local receipt/log hashes, and four independent exported-type/trust/axiom checks.')

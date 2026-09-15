from pathlib import Path
import hashlib, json, shutil, re

root=Path('/private/tmp/nla-formalization-ie17-20260915')
src=root/'linear-systems-and-elimination/IE-17/lean'
dst=Path('/private/tmp/nla-ie17-final-referee1')
dst.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=json.loads((src/'reviews/final-source-inputs.json').read_text())['input_sha256']
freeze=json.loads((src/'reviews/statement-freeze.json').read_text())['input_sha256']
for name,want in dict(inputs,**freeze).items():
    assert sha(src/name)==want,(name,sha(src/name),want)
    out=dst/name;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/name,out)
(dst/'.lake').mkdir()
(dst/'.lake/packages').symlink_to((src/'.lake/packages').resolve(),target_is_directory=True)
spec=(src/'Challenge.lean').read_text()
names=json.loads((src/'comparator.json').read_text())['theorem_names']
audit=['import Solution','noncomputable section','namespace NLA.IE17','set_option leancert.trust "kernel"']
for fullname in names:
    name=fullname.rsplit('.',1)[1]
    found=re.search(r'(?ms)^theorem '+re.escape(name)+r'(.*?) := by\n  sorry',spec)
    assert found,name
    args=' E c hc' if name=='spectralNorm_semantics' else ''
    audit.append('theorem referee1_'+name+found.group(1)+' := '+fullname+args)
    audit.append('#assert_trust kernel referee1_'+name)
    audit.append('#print axioms referee1_'+name)
for name in ['certificate_cutoffs','exists_optimal_error','feasible_direction_bounds','witnessE_feasible','witnessE_norm_sq_bound','lower_quadratic_certificate','zero_new_residual_certificate','optimal_error_bounds','penrose_projection_unique','penroseAt_correct','projection_norm_sq','actualQ_one_sq','actualQ_two_sq','approximation_error_values','witness_run_exact']:
    audit.extend(['#assert_trust kernel '+name,'#print axioms '+name])
audit.append('end NLA.IE17')
(dst/'AuditFull.lean').write_text('\n\n'.join(audit)+'\n')
extra={'../README.md':sha(src.parent/'README.md'),'../../../references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex':sha(root/'references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex'),'../../../docs/lean/REVIEW.md':sha(root/'docs/lean/REVIEW.md'),'reviews/final-source-inputs.json':sha(src/'reviews/final-source-inputs.json'),'reviews/statement-freeze.json':sha(src/'reviews/statement-freeze.json')}
(dst/'snapshot-inputs.json').write_text(json.dumps({'source':str(src),'candidate_inputs':inputs,'frozen_inputs':freeze,'additional_context':extra,'all_candidate_and_frozen_hashes_match':True,'proof_cache_copied':False,'dependency_cache':str((src/'.lake/packages').resolve()),'audit_sha256':sha(dst/'AuditFull.lean')},indent=2)+'\n')
print(json.dumps({'snapshot':str(dst),'candidate_input_count':len(inputs),'frozen_input_count':len(freeze),'all_hashes_match':True,'audited_exports':len(names)},indent=2))

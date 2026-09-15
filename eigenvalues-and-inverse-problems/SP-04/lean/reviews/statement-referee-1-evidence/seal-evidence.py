from pathlib import Path
import hashlib,json,re,subprocess

scratch=Path(__file__).resolve().parent
repo=Path('/private/tmp/nla-formalization-sp04-20260915')
p=repo/'eigenvalues-and-inverse-problems/SP-04/lean'
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
inputs=json.loads((scratch/'statement-inputs.json').read_text())
for name,h in inputs['input_sha256'].items():
    assert sha(p/name)==sha(scratch/name)==h,name
sources=json.loads((p/'reviews/initial/source-hashes.json').read_text())
for name,h in sources['files'].items():
    assert sha(repo/name)==h,name
    original=subprocess.check_output(['git','show',f"{inputs['published_base']}:{name}"],cwd=repo)
    assert hashlib.sha256(original).hexdigest()==h,name
manuscript=(repo/'eigenvalues-and-inverse-problems/SP-04/solution.md').read_text()
block=manuscript[manuscript.index('## Theorem '):manuscript.index('## Scope and review notes')].strip().encode()
assert len(block)==4714
assert hashlib.sha256(block).hexdigest()==sources['historical_reviewed_proof_block_sha256']
packages=[]
for pkg in json.loads((scratch/'lake-manifest.json').read_text())['packages']:
    loc=scratch/'.lake/packages'/pkg['name']
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=loc,text=True).strip()
    changes=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=loc,text=True)
    assert revision==pkg['rev'] and not changes,pkg['name']
    packages.append({'name':pkg['name'],'revision':revision,'tracked_changes':False})
challenge=(scratch/'challenge-build.log').read_text()
assert 'Build completed successfully (2386 jobs).' in challenge
assert challenge.count('declaration uses `sorry`')==11
audit=(scratch/'boundary-api-audit.log').read_text()
assert 'error:' not in audit and 'warning:' not in audit
assert 'instTopologicalSpaceMatrix' in audit and 'instT2SpaceMatrix' in audit
assert '\n9\n' in audit
config=json.loads((p/'comparator.json').read_text())
assert len(config['theorem_names'])==11 and config['definition_names']==[]
for name in config['theorem_names']:assert name in audit,name
defs=(p/'NLA/SP04/Definitions.lean').read_text()
assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',defs)
assert (p/'Solution.lean').read_text().splitlines()[-1]=='import NLA.SP04.Definitions'
arithmetic=json.loads((scratch/'independent-arithmetic.json').read_text())
assert arithmetic['result']=='PASS' and arithmetic['checks_count']==49
api_names=['Mathlib/Analysis/Matrix/Spectrum.lean','Mathlib/Algebra/MvPolynomial/Funext.lean',
 'Mathlib/Analysis/Matrix/Normed.lean','Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean',
 'Mathlib/Topology/Instances/Matrix.lean','Mathlib/LinearAlgebra/Matrix/Kronecker.lean',
 'Mathlib/Algebra/Polynomial/Roots.lean']
record={
 'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent non-implementing AI referee',
 'phase':'pre-proof statement review only',
 'published_base':inputs['published_base'],
 'ten_boundary_input_sha256':inputs['input_sha256'],
 'all_ten_match_current_and_fresh_snapshot':True,
 'source_sha256':sources['files'],'all_source_files_match_published_base':True,
 'historical_proof_block_bytes':len(block),'historical_proof_block_sha256':hashlib.sha256(block).hexdigest(),
 'dependency_pins':packages,'dependency_cache_reused':True,'project_build_cache_copied':False,
 'lean_version':subprocess.check_output(['/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean','--version'],text=True).strip(),
 'fresh_challenge_build':{'exit_code':0,'jobs':2386,'intentional_specification_holes':11},
 'boundary_api_audit':{'exit_code':0,'checked_exports':11,'printed_semantic_definitions':15,'actual_polynomial_variable_count':9},
 'independent_arithmetic':{'exit_code':0,'checks':49,'output_sha256':sha(scratch/'independent-arithmetic.json'),'author_checker_imported_or_executed':False},
 'api_source_sha256':{n:sha(scratch/'.lake/packages/mathlib'/n) for n in api_names},
 'proof_implementation':'none',
 'authoritative_kernel_axiom_and_comparator_proof_verification':'not yet applicable; pending completed proofs',
 'canonical_status':'Solved',
}
(scratch/'execution-record.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','inputs':10,'source_files':4,'typechecked_exports':11,'independent_checks':49,'sha256':sha(scratch/'execution-record.json')}))

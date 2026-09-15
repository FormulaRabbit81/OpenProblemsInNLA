from pathlib import Path
import hashlib, json, re, subprocess

scratch = Path(__file__).resolve().parent
repo = Path('/private/tmp/nla-formalization-pf02-20260915')
project = repo / 'nonnegative-and-positive-factorizations/PF-02/lean'
relative = project.relative_to(repo)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
inputs = json.loads((scratch / 'snapshot-inputs.json').read_text())
commit = inputs['candidate_commit']
matches = {}
for group in ['candidate_input_sha256', 'frozen_input_sha256']:
    for name, expected in inputs[group].items():
        assert sha(project / name) == expected, name
        assert sha(scratch / name) == expected, name
        committed = subprocess.check_output(['git','show',f'{commit}:{relative / name}'],cwd=repo)
        assert hashlib.sha256(committed).hexdigest() == expected, name
        matches[name] = expected
for name, expected in inputs['original_source_context_sha256'].items():
    assert sha(repo / name) == expected, name
    committed = subprocess.check_output(['git','show',f'{commit}:{name}'],cwd=repo)
    assert hashlib.sha256(committed).hexdigest() == expected, name

packages = []
for package in json.loads((scratch/'lake-manifest.json').read_text())['packages']:
    path = scratch/'.lake/packages'/package['name']
    head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
    changes = subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=path,text=True)
    assert head == package['rev'], package['name']
    assert not changes, (package['name'], changes)
    packages.append({'name':package['name'],'rev':head,'tracked_changes':False})

challenge = (scratch/'referee1-challenge-build.log').read_text()
solution = (scratch/'referee1-solution-build.log').read_text()
audit = (scratch/'referee1-audit-full.log').read_text()
assert 'Build completed successfully (2062 jobs).' in challenge
assert challenge.count('declaration uses `sorry`') == 9
assert 'Build completed successfully (3649 jobs).' in solution
assert 'warning:' not in solution and 'error:' not in solution
assert 'error:' not in audit and 'warning:' not in audit
axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",audit)
assert len(axioms) == 32
permitted = {'propext','Classical.choice','Quot.sound'}
assert all(set(a.split(', ')) <= permitted for _,a in axioms)
assert sum(n.startswith('NLA.PF02.referee1_') for n,_ in axioms) == 9
harness=(scratch/'AuditFull.lean').read_text()
assert harness.count('#assert_trust kernel') == 32
assert harness.count('#print axioms') == 32
assert 'instDiscreteTopologyBool' in audit
assert 'instTopologicalSpaceSubtype' in audit
assert 'instTopologicalSpaceQuot' in audit
for path in sorted((scratch/'NLA').rglob('*.lean'))+[scratch/'Solution.lean']:
    content = path.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by)\b', content), path
    assert not re.search(r'^\s*axiom\b', content, re.M), path
    assert 'import Challenge' not in content, path
assert 'PASS (9 declarations)' in (scratch/'referee1-manifest.log').read_text()
arithmetic=json.loads((scratch/'referee1-arithmetic.json').read_text())
assert arithmetic['result']=='PASS' and arithmetic['checks_count']==48

api_paths = [
 '.lake/packages/mathlib/Mathlib/Tactic/NormDet.lean',
 '.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean',
 '.lake/packages/mathlib/Mathlib/Tactic/Determinant/Bird/Cert.lean',
 '.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean',
 '.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Rank.lean',
 '.lake/packages/mathlib/Mathlib/Topology/Constructions.lean',
 '.lake/packages/mathlib/Mathlib/Topology/Instances/Matrix.lean',
 '.lake/packages/leancert/LeanCert/Tactic/Verification.lean',
]
record = {
 'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review (independent non-implementing AI agent)',
 'phase':'final source/local verification; not authoritative Linux/Comparator verification',
 'candidate_commit':commit,
 'input_match_to_worktree_snapshot_and_commit':True,
 'candidate_input_count':20,
 'frozen_input_count':10,
 'all_mathematical_source_bytes_unchanged':True,
 'source_context_unchanged':True,
 'dependency_packages':packages,
 'project_cache_copied':False,
 'fresh_challenge_build':{'exit_code':0,'jobs':2062,'intentional_specification_holes':9},
 'fresh_solution_build':{'exit_code':0,'jobs':3649,'warnings':0},
 'independent_type_trust_audit':{'exit_code':0,'exact_challenge_type_assignments':9,
   'kernel_trust_assertions':32,'transitive_axiom_lists':32,
   'permitted_axioms':sorted(permitted),'closure_results':dict(axioms)},
 'proof_token_scan':{'sorry':0,'admit':0,'native_decide':0,'unsafe':0,'implemented_by':0,'axiom_declarations':0},
 'lean_version':subprocess.check_output(['/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean','--version'],text=True).strip(),
 'api_source_sha256':{name:sha(scratch/name) for name in api_paths},
 'manifest_schema_coverage':{'exit_code':0,'declarations':9},
 'independent_arithmetic':{'exit_code':0,'checks':48,'polynomial_terms':120,
    'script_sha256':sha(scratch/'referee1-arithmetic.py'),
    'output_sha256':sha(scratch/'referee1-arithmetic.json')},
 'authoritative_linux_and_comparator':'pending',
}
(scratch/'execution-record.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','candidate_inputs':20,'frozen_inputs':10,
                  'kernel_closures':32,'dependency_pins':len(packages),
                  'record_sha256':sha(scratch/'execution-record.json')}))

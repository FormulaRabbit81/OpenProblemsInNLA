"""Independent KE-05 canonical runtime audit; does not execute Lean or mutate Git."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile

B = Path('/tmp/nla-lean-next-20260915')
O = B / 'reviews/KE05-mf22-independent/canonical35058392398-addendum'
R = B / 'canonical-runs/KE05-35058392398'
W = Path('/private/tmp/nla-lean-next-ke05-worktree')
P = 'randomized-and-low-rank-approximation/KE-05/lean'
C = '414371c9a76aafd7477d9705f9644f7efeb5e329'
HISTORICAL = '04f3f39beb69d77dbc4a8eadee70259eb89a591a'
REVIEWER = '/root/mf22_publication_referee'
O.mkdir(parents=True, exist_ok=True)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(path):
    return json.loads(path.read_text())

def dump(name, data):
    (O / name).write_text(json.dumps(data, indent=2) + '\n')

def git(*args):
    return subprocess.check_output(['git', '-C', str(W), *args])

def blob(commit, path):
    return git('show', commit + ':' + path)

prepared_path = B / 'KE05-CAMPAIGN-151-PREPARED.json'
assert sha(prepared_path.read_bytes()) == 'f480b7bf9756c7280eb664741e2d169a54d89060fe24891fe8d860c69b603010'
prepared = load(prepared_path)
old_path = B / 'KE05-CAMPAIGN-CANDIDATE.json'
assert sha(old_path.read_bytes()) == 'b625ea1c0e0f204c4d6af51b112c3e8474314fbe1c1bcd3d4d789fcb6cb9ee53'
prior = load(old_path)['files']
inputs = prepared['all_current_inputs']
assert len(prior) == 147 and len(inputs) == 151
assert all(inputs[k] == v for k, v in prior.items())
assert set(inputs) - set(prior) == set(prepared['new_inputs'])
for name, value in prepared['new_inputs'].items():
    original = B / 'reviews/KE05-mf22-import-candidate/reading-path-addendum' / Path(name).name
    assert sha(original.read_bytes()) == value

meta = load(R / 'run.json')
assert meta['id'] == 35058392398 and meta['head_sha'] == C
assert meta['status'] == 'completed' and meta['conclusion'] == 'success' and meta['event'] == 'push'
jobs = load(R / 'jobs.json')['jobs']
job, = [j for j in jobs if j['name'] == f'verify (KE-05, {P})']
assert job['id'] == 104673346252 and job['head_sha'] == C and job['conclusion'] == 'success'
assert all(s['conclusion'] == 'success' for s in job['steps'])
assert next(j for j in jobs if j['name'] == 'checker-controls')['conclusion'] == 'skipped'
E, = (R / 'artifacts/lean-KE-05').glob('verify-*')
result = load(E / 'result.json')
assert result['repository_commit'] == C and result['project'] == P
assert result['result'] == 'comparator-accepted' and result['semantic_review'] == 'not-performed-by-this-command'
assert result['input_sha256'] == inputs
tree = git('ls-tree', '-r', '--name-only', C, '--', P).decode().splitlines()
assert set(inputs) == {s[len(P) + 1:] for s in tree}
bindings = []
for name, digest in inputs.items():
    value = blob(C, P + '/' + name)
    assert sha(value) == digest and (W / P / name).read_bytes() == value
    bindings.append({'path': name, 'sha256': digest, 'bytes': len(value)})
dump('ALL-151-INPUT-BINDINGS.json', bindings)
math = [s for s in inputs if s in {'Challenge.lean', 'Solution.lean'} or s.startswith('NLA/') and s.endswith('.lean')]
assert len(math) == 23
for name in math:
    assert blob(C, P + '/' + name) == blob(HISTORICAL, P + '/' + name)
    assert inputs[name] == load(B / 'reviews/KE05-mf22-independent/ALL-23-SOURCES.json')[[x['path'] for x in load(B / 'reviews/KE05-mf22-independent/ALL-23-SOURCES.json')].index(name)]['sha256']
dump('ALL-23-UNCHANGED-MATH.json', [{'path': name, 'sha256': inputs[name]} for name in sorted(math)])
assert 'defaultTargets = ["Solution"]' in (W / P / 'lakefile.toml').read_text()
config = load(W / P / 'comparator.json')
assert config == result['config'] and len(config['theorem_names']) == 10
assert config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']

artifact, = load(R / 'artifacts.json')['artifacts']
archive = R / 'lean-KE-05.zip'
archive_hash = sha(archive.read_bytes())
assert artifact['id'] == 10431896877 and artifact['workflow_run']['head_sha'] == C
assert archive_hash == 'cb761990aabb0e62819bcfa4b8af9c8207ad4b504920ad5d27df06922c7708ce'
assert artifact['digest'] == 'sha256:' + archive_hash and not artifact['expired']
members = []
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():
        if name.endswith('/'):
            continue
        data = z.read(name)
        assert data == (R / 'artifacts/lean-KE-05' / name).read_bytes()
        members.append({'path': name, 'sha256': sha(data), 'bytes': len(data)})
assert len(members) == 13
dump('ALL-13-ARTIFACT-MEMBERS.json', members)
raw_path = R / 'job-104673346252.log'
raw = raw_path.read_text()
raw_lines = set(re.sub(r'^\d{4}-\d\d-\d\dT[0-9:.]+Z ', '', s) for s in raw.splitlines())
assert C in raw and archive_hash in raw and str(artifact['id']) in raw
log_checks = {}
for path in sorted(E.glob('*.log')):
    text = path.read_text()
    status = 1 if path.name in {'negative-native.log', 'negative-sorry.log'} else 0
    assert text.rstrip().endswith('EXIT_STATUS=' + str(status))
    payload = [s for s in text.splitlines() if s.strip() and not s.startswith('$ ') and not s.startswith('EXIT_STATUS=')]
    assert all(s in raw_lines for s in payload), path.name
    log_checks[path.name] = {'sha256': sha(path.read_bytes()), 'lines_read_in_full': len(text.splitlines()),
                             'expected_exit': status, 'payload_lines_bound_to_raw_job': len(payload)}
assert len(log_checks) == 9
dump('ACTUAL-LOG-CHECKS.json', log_checks)
comp = (E / 'comparator.log').read_text()
before, after = comp.split('Building Solution', 1)
assert len(re.findall(r'warning: Challenge\.lean:.*declaration uses `sorry`', before)) == 10
assert 'declaration uses `sorry`' not in after and 'sorryAx' not in comp and 'error:' not in comp
for module in ['Challenge', 'Solution']:
    line, = [s for s in comp.splitlines() if s.startswith('Exporting #[') and s.endswith(' from ' + module)]
    assert re.findall(r'NLA\.KE05\.\w+', line) == config['theorem_names']
axioms = dict(re.findall(r"'(NLA\.KE05\.[^']+)' depends on axioms: \[([^]]+)\]", after))
assert set(axioms) == set(config['theorem_names'])
assert all(set(v.split(', ')) == set(config['permitted_axioms']) for v in axioms.values())
for name in math:
    assert 'Built ' + name.removesuffix('.lean').replace('/', '.') + ' (' in comp
assert 'Built LeanCert.Tactic.Verification (' in comp
solution = (W / P / 'Solution.lean').read_text()
assert len(re.findall(r'^#assert_trust kernel NLA\.KE05\.', solution, re.M)) == 10
assert 'Lean default kernel accepts the solution' in after and 'Your solution is okay!' in after
assert "Illegal axiom detected: 'sorryAx'" in (E / 'negative-sorry.log').read_text()
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in (E / 'negative-native.log').read_text()

legacy_audit = R / 'ROOT-AUDIT.json'
assert sha(legacy_audit.read_bytes()) == '361ca6b180e239c5e1f98ae6994ab5d116b0f564f6a18105f56daeef85349975'
legacy = load(legacy_audit)
assert legacy['reviewer'] == '/root' and legacy['actual_checkout'] == C
assert legacy['bound_inputs'] == 151 and len(legacy['exports']) == 10
assert legacy['all_rejection_regression_sandbox_controls'] == 'PASS'
assert legacy['all_exports_permitted_axioms'] and legacy['literal_published_commit']
assert legacy['auditor_sha256'] == sha((B / 'audit_canonical_runtime.py').read_bytes())
for prefix in ['tools/lean', '.github/workflows/lean-verification.yml']:
    assert git('diff', 'ff6abf718126ceb23f933cf4f627f95104461fe8', C, '--', prefix) == b''
    assert git('diff', HISTORICAL, C, '--', prefix) == b''
lock = blob(C, 'tools/lean/source-lock.json')
assert sha(lock) == result['source_lock_sha256'] == result['tool_receipt']['source_lock_sha256']
pins = load(W / P / 'lake-manifest.json')['packages']
for pin in pins:
    assert pin['rev'] in (E / 'dependencies.log').read_text()
dump('EXECUTION-PROVENANCE.json', {
    'actual_executor_and_referee': REVIEWER,
    'legacy_file': str(legacy_audit), 'legacy_file_sha256': sha(legacy_audit.read_bytes()),
    'legacy_embedded_reviewer': '/root',
    'clarification': 'The unmodified shared auditor hard-codes reviewer=/root and filename ROOT-AUDIT.json. It was actually executed by /root/mf22_publication_referee for this run. This is not a second root execution or a second independent Lean run.',
    'auditor': str(B / 'audit_canonical_runtime.py'), 'auditor_sha256': legacy['auditor_sha256'],
    'fetcher': str(B / 'fetch_repository_run.py'), 'fetcher_sha256': sha((B / 'fetch_repository_run.py').read_bytes()),
    'local_Lean_or_Comparator': False})
dump('CHECKS.json', {
    'reviewer': REVIEWER, 'sealed_utc': datetime.now(timezone.utc).isoformat(),
    'verdict': 'ACCEPT fresh canonical runtime at literal 414371c9, combined with prior complete unchanged mathematical-source review',
    'run': meta['id'], 'run_url': meta['html_url'], 'job': job['id'], 'job_url': job['html_url'],
    'api_head_and_literal_checkout': C, 'event': meta['event'],
    'prepared_151_record_sha256': sha(prepared_path.read_bytes()),
    'all_151_prepared_Git_worktree_receipt_inputs_equal': True,
    'prior_147_inputs_unchanged': True, 'four_addendum_inputs_match_original_referee_packet': True,
    'all_23_mathematical_files_unchanged_from_prior_full_review_and_historical_commit': HISTORICAL,
    'default_target': 'Solution', 'Challenge_and_Solution_export_counts': [10, 10],
    'every_solution_export_axioms': config['permitted_axioms'],
    'LeanCert': 'Pinned 621a43d7; Tactic.Verification built and ten #assert_trust kernel checks executed. Exact algebraic formalization; no interval certificate claimed.',
    'kernel_replay_and_quotient_postcheck_controls': 'all three required behaviors passed',
    'Comparator_regressions': 'all five passed, including matching acceptance and mismatch/axiom rejection',
    'negative_sorry_and_native_axioms': 'both rejected with expected exit 1',
    'sandbox': 'UID1001 in both build/export; namespace, capabilities, AF_UNIX, write and malformed-option controls passed',
    'separate_checker_controls_job': 'skipped; required per-project controls actually ran and passed in verify job',
    'shared_harness_and_workflow_unchanged_from': ['ff6abf718126ceb23f933cf4f627f95104461fe8', HISTORICAL],
    'artifact_id': artifact['id'], 'artifact_sha256': archive_hash,
    'result_sha256': sha((E / 'result.json').read_bytes()),
    'all_13_archive_members_identical_to_extracted_files': True,
    'raw_job_sha256': sha(raw_path.read_bytes()),
    'nine_verification_logs_read_in_full': True,
    'verification_log_line_count': sum(v['lines_read_in_full'] for v in log_checks.values()),
    'all_payload_lines_bound_to_actual_raw_job': sum(v['payload_lines_bound_to_raw_job'] for v in log_checks.values()),
    'bootstrap_logs': 'All three read in full; expected exit0. Hashes retained in artifact-member inventory.',
    'cancelled_run_35058150211_used_as_acceptance': False,
    'original_authorship_preserved': 'Sidney Holden formalization; George Stepaniants mathematical argument/integration (Caltech CMS); Nian Shao original framework',
    'legacy_root_label_disclosed': 'EXECUTION-PROVENANCE.json',
    'local_Lean_or_Comparator_execution': False, 'Git_or_proof_edits': False, 'publication_or_count_change': False,
    'limitations': 'Audit of actual GitHub Linux execution, not another independently executed Lean run, a mathematical proof of the checker, formalized semantic translation, or a claim that any system is infallible. Prior full source-review judgments are carried forward only after exact byte matching.'})

manifest = {str(p.relative_to(O)): sha(p.read_bytes()) for p in sorted(O.rglob('*')) if p.is_file() and p.name != 'MANIFEST.json'}
dump('MANIFEST.json', {'kind': 'SHA256 inventory', 'files': manifest})
print(json.dumps({'verdict': 'ACCEPT', 'inputs': len(inputs), 'math_files': len(math), 'exports': 10,
                  'actual_payload_lines': sum(v['payload_lines_bound_to_raw_job'] for v in log_checks.values()),
                  'CHECKS_sha256': sha((O / 'CHECKS.json').read_bytes())}, indent=2))

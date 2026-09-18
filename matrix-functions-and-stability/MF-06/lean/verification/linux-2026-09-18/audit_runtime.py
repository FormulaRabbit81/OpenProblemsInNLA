"""Audit fetched canonical-run evidence; this does not rerun Lean or review mathematics."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

run = Path(sys.argv[1])
problem = sys.argv[2]
project = sys.argv[3]
published = sys.argv[4]
repo = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
trusted = 'ff6abf718126ceb23f933cf4f627f95104461fe8'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', *args], cwd=repo)

meta = json.loads((run / 'run.json').read_text())
assert meta['status'] == 'completed' and meta['conclusion'] == 'success'
receipts = list((run / 'artifacts' / ('lean-' + problem)).glob('verify-*/result.json'))
assert len(receipts) == 1
evidence = receipts[0].parent
result = json.loads(receipts[0].read_text())
actual = result['repository_commit']
assert result['project'] == project and result['result'] == 'comparator-accepted'
assert result['semantic_review'] == 'not-performed-by-this-command'
config = json.loads(git('show', actual + ':' + project + '/comparator.json'))
assert result['config'] == config
names = config['theorem_names']
assert names and len(names) == len(set(names))
assert config['definition_names'] == []
assert len(config['permitted_axioms']) == 3 and set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}

all_paths = git('ls-tree', '-r', '--name-only', actual, '--', project).decode().splitlines()
all_relative = {p[len(project) + 1:] for p in all_paths}
assert set(result['input_sha256']) == all_relative
for name, digest in result['input_sha256'].items():
    assert sha(git('show', actual + ':' + project + '/' + name)) == digest, name

for prefix in ['tools/lean', '.github/workflows/lean-verification.yml']:
    assert git('diff', trusted, actual, '--', prefix) == b'', prefix
    assert git('diff', actual, published, '--', prefix) == b'', prefix
lock = git('show', actual + ':tools/lean/source-lock.json')
assert sha(lock) == result['source_lock_sha256'] == result['tool_receipt']['source_lock_sha256']
tool = result['tool_receipt']
assert tool['platform'].startswith('Linux-')
assert tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert tool['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert 'x86_64-unknown-linux-gnu' in tool['lean_version']
logs = {p.name: p.read_text() for p in evidence.glob('*.log')}

positive = ['comparator.log', 'kernel-controls.log', 'comparator-controls.log',
            'sandbox.log', 'dependencies.log', 'mathlib-cache.log', 'user-service.log']
for name in positive:
    assert logs[name].rstrip().endswith('EXIT_STATUS=0'), name
comp = logs['comparator.log']
for module in ['Challenge', 'Solution']:
    lines = [s for s in comp.splitlines() if s.startswith('Exporting #[') and s.endswith(' from ' + module)]
    assert len(lines) == 1, module
    actual_names = re.findall(r'\bNLA\.[A-Za-z0-9_.]+', lines[0])
    assert actual_names == names, (module, actual_names)
for name in names:
    matches = re.findall(re.escape("'" + name + "' depends on axioms: ") + r'\[([^\]]*)\]', comp)
    assert matches, name
    for axioms in matches:
        assert set(axioms.split(', ')) <= set(config['permitted_axioms']), (name, axioms)
assert comp.index('Building Challenge') < comp.index('Building Solution') < comp.index('Running Lean default kernel on solution.')
assert comp.count('declaration uses `sorry`') == len(names)
assert 'declaration uses `sorry`' not in comp[comp.index('Building Solution'):]
assert 'sorryAx' not in comp and 'Illegal axiom' not in comp and 'error:' not in comp
assert 'Lean default kernel accepts the solution' in comp
assert comp.count('Your solution is okay!') == 1

for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
               'RETURN invalid_raw_proof: rejected:',
               'RETURN quotient_postcheck_mismatch: rejected:',
               'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
    assert marker in logs['kernel-controls.log'], marker
for fixture in ['simple_match', 'simple_mismatch', 'simple_axiom_issue',
                'simple_kind_mismatch', 'type_mismatch']:
    assert 'PASS ' + fixture + ':' in logs['comparator-controls.log'], fixture
assert 'PASS: all five Comparator regressions' in logs['comparator-controls.log']
assert "Illegal axiom detected: 'sorryAx'" in logs['negative-sorry.log']
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in logs['negative-native.log']
for name in ['negative-sorry.log', 'negative-native.log']:
    assert logs[name].rstrip().endswith('EXIT_STATUS=1'), name

uids = [int(n) for n in re.findall(r'Sandbox UID: (\d+)', logs['sandbox.log'])]
assert uids == [1001, 1001]
for marker in ['MODE build: exit=0', 'MODE export: exit=0',
               'PASS effective capabilities: none', 'PASS AF_UNIX socket creation: denied',
               'PASS no_new_privs: set', 'PASS user namespace: private',
               'PASS pid namespace: private', 'PASS mnt namespace: private',
               'PASS net namespace: private', 'PASS ipc namespace: private',
               'PASS uts namespace: private', 'PASS export .lake write-open: denied',
               'Outer and export fixture contents unchanged; only designated build fixture written.']:
    assert marker in logs['sandbox.log'], marker
manifest = json.loads(git('show', actual + ':' + project + '/lake-manifest.json'))
for dep in manifest['packages']:
    assert dep['rev'] in logs['dependencies.log'], dep['name']

jobs = json.loads((run / 'jobs.json').read_text())['jobs']
matching = [j for j in jobs if j['name'] == f'verify ({problem}, {project})']
assert len(matching) == 1
job = matching[0]
assert job['conclusion'] == 'success'
assert all(s['conclusion'] in ['success', 'skipped'] for s in job['steps'])
raw_path = run / f"job-{job['id']}.log"
raw = raw_path.read_text()
assert re.search(r'git log -1 --format=%H\n[^\n]*' + re.escape(actual) + r'\n', raw)
for marker in ['Building Solution', names[-1], 'PASS: fresh Comparator run and all controls.']:
    assert marker in raw, marker

arts = json.loads((run / 'artifacts.json').read_text())['artifacts']
arts = [a for a in arts if a['name'] == 'lean-' + problem]
assert len(arts) == 1
artifact = arts[0]
archive = run / ('lean-' + problem + '.zip')
assert artifact['digest'] == 'sha256:' + sha(archive.read_bytes())
assert artifact['workflow_run']['head_sha'] == meta['head_sha']
assert not artifact['expired']

report = {
    'reviewer': '/root',
    'verdict': 'ACCEPT actual runtime evidence; separate complete mathematical source review required',
    'run': meta['id'], 'job': job['id'], 'problem': problem, 'project': project,
    'actual_checkout': actual, 'api_head': meta['head_sha'], 'event': meta['event'],
    'literal_published_commit': actual == published,
    'bound_inputs': len(result['input_sha256']), 'all_tracked_project_inputs_checked': True,
    'exports': names, 'all_exports_permitted_axioms': True,
    'default_kernel_and_comparator': 'PASS',
    'all_rejection_regression_sandbox_controls': 'PASS', 'nonroot_uids': uids,
    'artifact_id': artifact['id'], 'artifact_sha256': sha(archive.read_bytes()),
    'source_lock_sha256': sha(lock), 'shared_checker_unchanged_from_accepted_commit': trusted,
    'actual_job_log_sha256': sha(raw_path.read_bytes()),
    'raw_logs_sha256': {p.name: sha(p.read_bytes()) for p in sorted(evidence.glob('*.log'))},
    'auditor_sha256': sha(Path(__file__).read_bytes()),
    'local_lean_execution': False,
    'scope': 'Audit of an authenticated GitHub execution, not another independently executed Lean run or certification of checker infallibility.'
}
output = run / 'ROOT-AUDIT.json'
data = (json.dumps(report, indent=2) + '\n').encode()
if output.exists():
    assert output.read_bytes() == data
else:
    with tempfile.NamedTemporaryFile(dir=run, delete=False) as f:
        f.write(data); f.flush(); os.fsync(f.fileno()); name = f.name
    os.replace(name, output)
print(json.dumps({'run': meta['id'], 'actual_checkout': actual, 'inputs': report['bound_inputs'],
                  'exports': len(names), 'runtime_accepted': True,
                  'root_audit_sha256': sha(data)}, indent=2))

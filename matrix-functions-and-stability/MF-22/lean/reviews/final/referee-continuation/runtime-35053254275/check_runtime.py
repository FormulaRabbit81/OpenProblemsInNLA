from pathlib import Path
import datetime, hashlib, io, json, re, subprocess, zipfile

R = Path(__file__).parent
prior = R.parent
W = Path('/private/tmp/nla-lean-next-mf22-worktree')
D = Path('/tmp/nla-lean-next-20260915/canonical-runs/MF22-35053254275')
revision = 'c701bfeea660473fc31ad9d0c74b76309be3b49f'
project = 'matrix-functions-and-stability/MF-22/lean'
sha = lambda b: hashlib.sha256(b).hexdigest()
filehash = lambda p: sha(p.read_bytes())
load = lambda p: json.loads(p.read_text())
def git(*args):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(W), *args])
previous = load(prior / 'CHECKS.json')
assert filehash(prior / 'CHECKS.json') == 'd9bda16fb6cf028b2edde19d5bffdd905963d902a683f290aed362369c6605b7'
assert filehash(prior / 'REVIEW.md') == 'bbbfdec513fc330f35895d5d07a3eadc31bb97f317bc8a52c33576e01d8ed274'
assert previous['revision'] == revision
run = load(D / 'run.json')
jobs = load(D / 'jobs.json')['jobs']
artifacts = load(D / 'artifacts.json')['artifacts']
assert run['id'] == 35053254275 and run['head_sha'] == revision
assert run['event'] == 'push' and run['status'] == 'completed' and run['conclusion'] == 'success'
job = next(j for j in jobs if j['name'] == 'verify (MF-22, ' + project + ')')
assert job['id'] == 104658059786 and job['head_sha'] == revision and job['conclusion'] == 'success'
assert next(s for s in job['steps'] if s['name'] == 'Fresh sandboxed statement, axiom and kernel verification')['conclusion'] == 'success'
assert next(j for j in jobs if j['name'] == 'checker-controls')['conclusion'] == 'skipped'
archive = D / 'lean-MF-22.zip'
artifact = next(a for a in artifacts if a['name'] == 'lean-MF-22')
assert artifact['id'] == 10429509734
assert artifact['digest'] == 'sha256:' + filehash(archive)
assert filehash(archive) == '09569ed6a546db076f38bbfae867dbdc278a398c78811175dfbc4371fd7433ca'
assert artifact['workflow_run']['head_sha'] == revision
assert not artifact['expired']
with zipfile.ZipFile(archive) as z:
    members = [n for n in z.namelist() if not n.endswith('/')]
    assert len(members) == 13
    for n in members:
        assert z.read(n) == (D / 'artifacts/lean-MF-22' / n).read_bytes(), n
results = list((D / 'artifacts/lean-MF-22').glob('verify-*/result.json'))
assert len(results) == 1
E = results[0].parent
receipt = load(results[0])
assert receipt['repository_commit'] == revision and receipt['project'] == project
assert receipt['result'] == 'comparator-accepted'
assert receipt['semantic_review'] == 'not-performed-by-this-command'
inputs = receipt['input_sha256']
tracked = git('ls-tree', '-r', '--name-only', revision, '--', project).decode().splitlines()
assert set(inputs) == {n[len(project) + 1:] for n in tracked} and len(inputs) == 634
# One read-only Git batch authenticates every project blob, including histories.
names = sorted(inputs)
request = ''.join(revision + ':' + project + '/' + n + '\n' for n in names).encode()
stream = io.BytesIO(subprocess.check_output(['git', '-C', str(W), 'cat-file', '--batch'], input=request))
for n in names:
    header = stream.readline().decode().split()
    assert len(header) == 3 and header[1] == 'blob', n
    content = stream.read(int(header[2]))
    assert stream.read(1) == b'\n' and sha(content) == inputs[n], n
assert stream.read() == b''
for n, h in previous['source_sha256'].items():
    assert inputs[n] == h, n
config = json.loads(git('show', revision + ':' + project + '/comparator.json'))
assert receipt['config'] == config and config['definition_names'] == []
exports = config['theorem_names']
assert len(exports) == len(set(exports)) == 22
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(config['permitted_axioms']) == allowed
tool = receipt['tool_receipt']
lock = git('show', revision + ':tools/lean/source-lock.json')
assert sha(lock) == receipt['source_lock_sha256'] == tool['source_lock_sha256']
assert tool['platform'].startswith('Linux-') and tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert 'x86_64-unknown-linux-gnu' in tool['lean_version']
assert tool['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
for scope in ['tools/lean', '.github/workflows/lean-verification.yml']:
    assert git('diff', 'ff6abf718126ceb23f933cf4f627f95104461fe8', revision, '--', scope) == b''
logs = {p.name:p.read_text() for p in E.glob('*.log')}
positive = ['comparator.log','kernel-controls.log','comparator-controls.log','sandbox.log',
    'dependencies.log','mathlib-cache.log','user-service.log']
for n in positive:
    assert logs[n].rstrip().endswith('EXIT_STATUS=0'), n
comp = logs['comparator.log']
for module in ['Challenge','Solution']:
    export_lines = [l for l in comp.splitlines() if l.startswith('Exporting #[') and l.endswith(' from ' + module)]
    assert len(export_lines) == 1
    assert re.findall(r'\bNLA\.MF22\.[A-Za-z0-9_]+',export_lines[0]) == exports
solution_log = comp[comp.index('Building Solution'):]
assert not re.search(r'^error:',comp,re.M)
assert 'declaration uses `sorry`' not in solution_log
assert comp.count('declaration uses `sorry`') == 22
assert comp.count('Lean default kernel accepts the solution') == 1
assert comp.count('Your solution is okay!') == 1
assert comp.index('Building Solution') < comp.index('Running Lean default kernel on solution.')
measured = dict(re.findall(r"info: Solution\.lean:\d+:0: '(NLA\.MF22\.[^']+)' depends on axioms: \[([^\]]*)\]",comp))
assert set(measured) == set(exports)
assert all(set(v.split(', ')) == allowed for v in measured.values())
assert 'sorryAx' not in comp and 'Illegal axiom' not in comp
kernel_markers = [
 'RETURN honest_with_inductives_and_quotients: accepted',
 'RETURN invalid_raw_proof: rejected:',
 'RETURN quotient_postcheck_mismatch: rejected:',
 'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']
assert all(m in logs['kernel-controls.log'] for m in kernel_markers)
for fixture in ['simple_match','simple_mismatch','simple_axiom_issue','simple_kind_mismatch','type_mismatch']:
    assert 'PASS ' + fixture + ':' in logs['comparator-controls.log']
assert 'PASS: all five Comparator regressions' in logs['comparator-controls.log']
for n, marker in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),
    ('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
    assert marker in logs[n] and logs[n].rstrip().endswith('EXIT_STATUS=1')
sandbox = logs['sandbox.log']
assert re.findall(r'Sandbox UID: (\d+)',sandbox) == ['1001','1001']
for marker in ['MODE build: exit=0','MODE export: exit=0',
    'PASS effective capabilities: none','PASS no_new_privs: set',
    'PASS AF_UNIX socket creation: denied','PASS user namespace: private',
    'PASS pid namespace: private','PASS mnt namespace: private','PASS net namespace: private',
    'PASS ipc namespace: private','PASS uts namespace: private',
    'PASS host parent: absent from private /proc','PASS host parent signal lookup: denied',
    'PASS host loopback listener: unreachable','PASS export .lake write-open: denied',
    'PASS nested namespace write attempt: rejected exit=1',
    'Outer and export fixture contents unchanged; only designated build fixture written.']:
    assert marker in sandbox, marker
for case in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']:
    assert 'NEGATIVE ' + case + ': exit=2' in sandbox
manifest = json.loads(git('show',revision + ':' + project + '/lake-manifest.json'))
for package in manifest['packages']:
    assert package['rev'] in logs['dependencies.log'], package['name']
raw = (D / 'job-104658059786.log').read_text(encoding='utf-8-sig')
assert re.search(r'git log -1 --format=%H\n[^\n]*' + revision + r'\n',raw)
assert 'PASS: fresh Comparator run and all controls.' in raw
assert artifact['digest'][7:] in raw and str(artifact['id']) in raw
raw_payload = '\n'.join(re.sub(r'^\d{4}-\d\d-\d\dT[0-9:.]+Z ', '',l) for l in raw.splitlines())
payload_lines = set(raw_payload.splitlines())
checked_payload = 0
for n, log in logs.items():
    for line in log.splitlines():
        if not line or line.startswith('$ ') or line.startswith('EXIT_STATUS='):
            continue
        assert line in payload_lines, (n,line)
        checked_payload += 1
out = {
 'reviewer':'/root/mf22_publication_referee',
 'reviewer_type':'independent nonimplementing OpenAI Codex referee',
 'created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'verdict':'approve actual canonical runtime evidence for the fully reviewed MF-22 source',
 'run':35053254275,'job':104658059786,'revision':revision,'project':project,
 'prior_complete_source_report_sha256':filehash(prior/'REVIEW.md'),
 'prior_complete_source_checks_sha256':filehash(prior/'CHECKS.json'),
 'source_file_count_unchanged':29,'all_tracked_project_Git_blobs_verified':634,
 'artifact_id':10429509734,'artifact_sha256':filehash(archive),
 'all_13_extracted_artifact_members_byte_matched':True,
 'result_sha256':filehash(results[0]),
 'raw_job_sha256':filehash(D/'job-104658059786.log'),
 'raw_control_and_comparator_lines_cross_matched_to_job':checked_payload,
 'all_22_comparator_targets':exports,'default_kernel_acceptance':True,
 'all_22_actual_export_axioms':sorted(allowed),
 'all_actual_per_project_controls_passed':True,
 'separate_checker_controls_job':'skipped; required controls ran inside successful project verify job',
 'source_lock_sha256':sha(lock),'nonroot_sandbox_uids':[1001,1001],
 'harness_and_workflow_unchanged_from':'ff6abf718126ceb23f933cf4f627f95104461fe8',
 'raw_logs_sha256':{p.name:filehash(p) for p in sorted(E.glob('*.log'))},
 'local_Lean_or_Lake_executed':False,
 'is_an_independently_executed_second_Lean_run':False,
 'limits':'Independent audit of the authenticated GitHub run and reviewed source, not a guarantee of checker or platform infallibility. No later publication revision is automatically covered.',
 'published_PR_or_count_changed_by_reviewer':False
}
(R/'CHECKS.json').open('x').write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'verdict':out['verdict'],'inputs':634,'exports':22,
 'cross_matched_log_lines':checked_payload,'CHECKS_sha256':filehash(R/'CHECKS.json')},indent=2))

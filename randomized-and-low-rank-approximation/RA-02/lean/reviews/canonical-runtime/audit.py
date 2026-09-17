"""Read-only audit of retained GitHub execution; writes only this review directory.

This does not execute Lean, Lake, Comparator, a cache, Git mutation, or the prior
generic helper. The independent reviewer reads full logs separately. Git show,
ls-tree and diff supply read-only literal object evidence.
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
CFG = json.loads((OUT / 'config.json').read_text())
P = Path(CFG['packet'])
W = Path(CFG['worktree'])
REL = CFG['project']
HEAD = CFG['commit']
PROBLEM = CFG['problem']
NS = CFG['namespace']
TRUSTED = 'ff6abf718126ceb23f933cf4f627f95104461fe8'
A = P / 'artifacts' / ('lean-' + PROBLEM)
bindings = {}
gitmap = {}
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check(value, label):
    if not value:
        raise AssertionError(label)
    checks.append(label)


def read(path):
    path = Path(path)
    data = path.read_bytes()
    bindings[str(path)] = sha(data)
    return data


def js(path):
    return json.loads(read(path))


def git(*args):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(W), *args])


def blob(path):
    data = git('show', HEAD + ':' + REL + '/' + path)
    gitmap[path] = sha(data)
    return data


run, jobs, artifacts, fetch = [js(P / n) for n in ['run.json', 'jobs.json', 'artifacts.json', 'FETCH-IDENTITY.json']]
check(run['id'] == CFG['run'] and run['head_sha'] == HEAD and run['event'] == 'push', 'literal push run identity')
check(run['status'] == 'completed' and run['conclusion'] == 'success' and run['run_attempt'] == 1, 'successful completed attempt one')
check(run['repository']['full_name'] == 'sgstepaniants/OpenProblemsInNLA', 'repository identity')
check(run['path'] == '.github/workflows/lean-verification.yml', 'verification workflow identity')
check(fetch['run'] == run['id'] and fetch['commit'] == HEAD and fetch['conclusion'] == 'success', 'prior authenticated fetch identity')
receipts = list(A.glob('verify-*/result.json'))
check(len(receipts) == 1, 'one execution receipt')
E = receipts[0].parent
r = js(receipts[0])
check(r['repository_commit'] == HEAD and r['project'] == REL and r['result'] == 'comparator-accepted', 'receipt literal checkout and acceptance')
check(r['semantic_review'] == 'not-performed-by-this-command', 'receipt does not claim semantic review')
inputs = r['input_sha256']
tree = git('ls-tree', '-r', HEAD, '--', REL).decode().splitlines()
paths = []
for line in tree:
    info, path = line.split('\t', 1)
    mode, kind, oid = info.split()
    check(mode in ['100644', '100755'] and kind == 'blob', 'ordinary tracked input ' + path)
    paths.append(path[len(REL) + 1:])
check(len(inputs) == CFG['input_count'] and set(paths) == set(inputs), 'all and only tracked project inputs in receipt')
for path, digest in inputs.items():
    check(sha(blob(path)) == digest, 'literal Git input hash ' + path)
    check(sha(read(W / REL / path)) == digest, 'worktree input byte identity ' + path)
for prefix in ['tools/lean', '.github/workflows/lean-verification.yml']:
    check(git('diff', '--exit-code', TRUSTED, HEAD, '--', prefix) == b'', 'unchanged shared checker ' + prefix)
shared = git('ls-tree', '-r', '--name-only', HEAD, '--', 'tools/lean', '.github/workflows/lean-verification.yml').decode().splitlines()
shared_hashes = {p: sha(git('show', HEAD + ':' + p)) for p in shared}
for p, digest in shared_hashes.items():
    check(sha(read(W / p)) == digest, 'shared checker worktree identity ' + p)
lock = json.loads(git('show', HEAD + ':tools/lean/source-lock.json'))
lockhash = shared_hashes['tools/lean/source-lock.json']
tool = r['tool_receipt']
check(lockhash == r['source_lock_sha256'] == tool['source_lock_sha256'], 'source-lock receipt binding')
check(tool['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62', 'pinned Forsythe revision')
check(tool['platform'].startswith('Linux-') and 'x86_64-unknown-linux-gnu' in tool['lean_version'], 'actual Linux tool receipt')
check(tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1', 'pinned Lean version')
check(set(tool['executables']) == {'.tools/comparator/.lake/build/bin/comparator', '.tools/lean4export/.lake/build/bin/lean4export', '.tools/bin/landrun'}, 'checker executable hashes retained')
config = json.loads(blob('comparator.json'))
check(config == r['config'], 'exact Comparator configuration')
names = config['theorem_names']
check(len(names) == len(set(names)) == CFG['export_count'], 'exact distinct export count')
check(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution', 'canonical module names')
check(config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound'] and config['definition_names'] == [], 'standard three axioms and no definition holes')
freeze = json.loads(blob('STATEMENT-FREEZE.json'))
frozen = freeze.get('frozen_files', freeze.get('frozen_files_sha256'))
check(len(frozen) == CFG['frozen_count'], 'frozen input count')
for path, digest in frozen.items():
    check(sha(blob(CFG['snapshot'] + '/' + path)) == digest, 'original frozen snapshot ' + path)
    if path != 'lakefile.toml':
        check(inputs[path] == digest, 'unchanged active frozen input ' + path)
oldlake = blob(CFG['snapshot'] + '/lakefile.toml')
check(oldlake.replace(b'defaultTargets = ["Challenge"]', b'defaultTargets = ["Solution"]') + b'\n[[lean_lib]]\nname = "Solution"\n' == blob('lakefile.toml'), 'sole active Lake transition is Solution default and library registration')
local = json.loads(blob('verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json'))
math = local['accepted_source_sha256']
check(len(math) == CFG['source_count'], 'accepted mathematical source count')
for path, digest in math.items():
    check(inputs[path] == digest, 'same local accepted source bytes ' + path)
    check(sha(read(local['selected_source_locations'][path])) == digest, 'same source origin bytes ' + path)
manifest = json.loads(blob('lake-manifest.json'))
pins = {x['name']: x['rev'] for x in manifest['packages']}
check(pins == local['dependency_commits'] and len(pins) == 10, 'exact ten dependency pins preserved')
solution = blob('Solution.lean').decode()
check('import Challenge' not in solution, 'Solution does not import Challenge')
for command in ['#print axioms', '#assert_trust kernel']:
    actual = re.findall(r'^' + re.escape(command) + r' (\S+)', solution, re.M)
    actual = [n if n.startswith('NLA.') else NS + '.' + n for n in actual]
    check(actual == names, 'complete ordered wrapper ' + command)
closure = set()


def walk(module):
    path = module.replace('.', '/') + '.lean'
    if path not in math or path in closure:
        return
    closure.add(path)
    for imp in re.findall(r'^import ([\w.]+)', blob(path).decode(), re.M):
        walk(imp)


walk('Solution')
check(len(closure) == CFG['closure_count'], 'independently reconstructed final import closure')
numerical = blob('NLA/' + PROBLEM.replace('-', '') + '/Numerical.lean').decode()
check('set_option leancert.trust "kernel"' in numerical and 'interval_decide (trust := kernel)' in numerical, 'explicit kernel-mode LeanCert certificate')
check('_ ≤ 3 := exp_one_bound' in numerical, 'RA02 numerical certificate consumer retained')
check('rank_denominator_le_three r' in blob('NLA/RA02/ExponentialComparison.lean').decode(), 'RA02 tail bound consumes numerical estimate')
check('exponential_tail_factor r hr' in blob('NLA/RA02/FinalCounterexample.lean').decode(), 'RA02 final theorem consumes tail bound')
# All nine standards were just read in the preceding SF01 audit. RA02 retains
# identical bytes; its provenance schema differs and is not silently assumed
# to contain SF01's standards array. Bind this equality to the sealed SF01 map.
std_ref = OUT.parent / 'SF01-runtime-referee-35175258802'
std_manifest_data = read(std_ref / 'MANIFEST.json')
check(sha(std_manifest_data) == 'a2015c419716da0de1b13a0390d6fd5d0e1cb0d0ea2e5ee393bf393ab5551ffa', 'sealed prior standards reference identity')
std_manifest = json.loads(std_manifest_data)
std_map_data = read(std_ref / 'GIT-INPUTS.json')
check(sha(std_map_data) == std_manifest['files']['GIT-INPUTS.json'], 'sealed prior standards Git map identity')
std_map = json.loads(std_map_data)['sha256']
standards = {p: h for p, h in inputs.items() if p.startswith('sources/standards/')}
check(len(standards) == 9, 'all nine pinned standard snapshots')
for path, digest in standards.items():
    check(digest == std_map[path], 'identical already-read pinned standard ' + path)
review_index = json.loads(blob('reviews/INDEX.json'))
preserved_reviews = {}
for item in review_index.get('reports', []):
    check(inputs[item['path']] == item['sha256'], 'retained historical review ' + item['path'])
for item in review_index['current_attached_reviews'] + review_index['final_reviews']:
    directory = str(Path(item['path']).parent)
    check(inputs[directory + '/MANIFEST.json'] == item['manifest_sha256'], 'current review manifest ' + directory)
    inventory = json.loads(blob(directory + '/MANIFEST.json'))
    for path, digest in inventory['files'].items():
        if isinstance(digest, dict):
            digest = digest['sha256']
        check(inputs[directory + '/' + path] == digest, 'sealed review payload ' + directory + '/' + path)
    preserved_reviews[directory] = item['manifest_sha256']
source_map = json.loads(blob(CFG['full_source_review'] + '/SOURCE-MAP.json'))
transported_map = {('Solution.lean' if p == 'NLA/RA02/Complete.lean' else p): v['sha256'] for p, v in source_map.items()}
check(transported_map == math, 'first complete nonauthor source map equals accepted/runtime bytes with exact wrapper filename transport')
second_source_map = json.loads(blob('reviews/final/RA02-ie13-final-local-development19/SELECTED-SOURCE-PATHS.json'))
check({p: v['sha256'] for p, v in second_source_map.items()} == math, 'second complete nonauthor source map equals accepted/runtime bytes')
logs = {p.name: read(p).decode() for p in sorted(A.rglob('*.log'))}
check(len(logs) == 12 and CFG['manual_complete_log_read'], 'twelve complete artifact logs manually read')
for name, data in logs.items():
    status = re.findall(r'^EXIT_STATUS=(\d+)$', data, re.M)
    check(status == (['1'] if name in ['negative-sorry.log', 'negative-native.log'] else ['0']), 'expected recorded log status ' + name)
comp = logs['comparator.log']
check(comp.index('Building Challenge') < comp.index('Building Solution') < comp.index('Running Lean default kernel on solution.'), 'fresh Challenge then Solution then kernel sequence')
check(comp.count('declaration uses `sorry`') == len(names) and 'declaration uses `sorry`' not in comp[comp.index('Building Solution'):], 'only intentional Challenge holes')
check(not any(x in comp for x in ['sorryAx', 'Illegal axiom', 'error:']), 'no forbidden proof axiom or compiler error')
for module in ['Challenge', 'Solution']:
    lines = [s for s in comp.splitlines() if s.startswith('Exporting #[') and s.endswith(' from ' + module)]
    check(len(lines) == 1 and re.findall(r'\bNLA\.[\w.]+', lines[0]) == names, 'exact ordered exported theorem list ' + module)
prints = re.findall(r"info: Solution\.lean:\d+:0: '(NLA\.[\w.]+)' depends on axioms: \[([^\]]*)\]", comp)
check([p[0] for p in prints] == names, 'one ordered Solution axiom report per export')
check(all(set(p[1].split(', ')) == set(config['permitted_axioms']) for p in prints), 'all Solution reports contain exactly standard three axioms')
check('Lean default kernel accepts the solution' in comp and comp.count('Your solution is okay!') == 1, 'actual default kernel and Comparator accept')
built = set(re.findall(r'Built (NLA\.[\w.]+) \(', comp))
check(built == {p[:-5].replace('/', '.') for p in closure if p.startswith('NLA/')}, 'fresh actual build of every final local module')
check('Built Solution (' in comp, 'actual canonical Solution build')
for marker in ['RETURN honest_with_inductives_and_quotients: accepted', 'RETURN invalid_raw_proof: rejected:', 'RETURN quotient_postcheck_mismatch: rejected:', 'Quotient post-check rejects the solution', 'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
    check(marker in logs['kernel-controls.log'], 'kernel control ' + marker)
for name, status in [('simple_match', 0), ('simple_mismatch', 1), ('simple_axiom_issue', 1), ('simple_kind_mismatch', 1), ('type_mismatch', 1)]:
    check(f'PASS {name}: exit {status}, expected {status}; required phase:' in logs['comparator-controls.log'], 'Comparator regression ' + name)
check('PASS: all five Comparator regressions' in logs['comparator-controls.log'], 'all five Comparator regressions complete')
for name, marker in [('negative-sorry.log', "Illegal axiom detected: 'sorryAx'"), ('negative-native.log', "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
    check(marker in logs[name], 'expected forbidden axiom rejection ' + name)
sandbox = logs['sandbox.log']
check(re.findall(r'Sandbox UID: (\d+)', sandbox) == ['1001', '1001'], 'both actual sandbox modes UID1001')
for mode in ['build', 'export']:
    block = sandbox.split('MODE ' + mode + ': exit=0', 1)[1].split('\n\n', 1)[0]
    for marker in ['PASS outside .lake write-open: denied', 'PASS outside .lake truncate: denied', 'PASS outside .lake read-only truncate-open: denied', 'PASS symlink from .lake to outside write: denied', 'PASS outside .lake creation: denied', 'PASS user namespace: private', 'PASS pid namespace: private', 'PASS mnt namespace: private', 'PASS net namespace: private', 'PASS ipc namespace: private', 'PASS uts namespace: private', 'PASS host parent: absent from private /proc', 'PASS host parent signal lookup: denied', 'PASS host loopback listener: unreachable', 'PASS AF_UNIX socket creation: denied', 'PASS effective capabilities: none', 'PASS no_new_privs: set', 'PASS nested namespace write attempt: rejected exit=1']:
        check(marker in block, 'sandbox ' + mode + ' ' + marker)
check('PASS build .lake write: allowed' in sandbox and 'PASS export .lake write-open: denied' in sandbox and 'PASS export .lake truncate: denied' in sandbox, 'differentiated build and export writes')
for case in ['unknown option', 'unexpected --rw', 'unexpected --rwx', 'relative --rwx']:
    check('NEGATIVE ' + case + ': exit=2' in sandbox, 'sandbox invalid argument rejection ' + case)
check('Outer and export fixture contents unchanged; only designated build fixture written.' in sandbox, 'sandbox fixture postchecks')
for logname in ['comparator.log', 'negative-sorry.log', 'negative-native.log', 'user-service.log']:
    check("RestrictAddressFamilies=~AF_UNIX" in logs[logname] and 'strict_landrun.py' in logs[logname], 'restricted real command ' + logname)
for name, rev in pins.items():
    check(f"info: {name}: checking out revision '{rev}'" in logs['dependencies.log'], 'actual dependency checkout ' + name)
check('Decompressed 8690 file(s)' in logs['mathlib-cache.log'] and 'leanprover-community/mathlib4' in logs['mathlib-cache.log'], 'actual pinned dependency cache retrieval')
job = next(x for x in jobs['jobs'] if x['id'] == CFG['job'])
check(job['head_sha'] == HEAD and job['conclusion'] == 'success' and job['name'] == f'verify ({PROBLEM}, {REL})', 'actual verification job identity')
check(all(s['conclusion'] in ['success', 'skipped'] for s in job['steps']), 'verification job steps complete')
check(len(jobs['jobs']) == 3 and len([j for j in jobs['jobs'] if j['name'].startswith('verify')]) == 1, 'single project verify job')
check(next(j for j in jobs['jobs'] if j['name'] == 'checker-controls')['conclusion'] == 'skipped', 'standalone unchanged-checker job skipped')
raw = read(P / f"job-{CFG['job']}.log").decode()
check(re.search(r'git log -1 --format=%H\n[^\n]*' + re.escape(HEAD) + r'\n', raw), 'raw actual literal checkout')
check('PASS: fresh Comparator run and all controls.' in raw, 'actual job final acceptance marker')
selector = read(P / f"job-{CFG['selector_job']}.log").decode()
selected = json.dumps({'include': [{'id': PROBLEM, 'project': REL}]}, separators=(',', ':'))
check(selected in selector, 'actual selector chose only this project')
ansi = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')


def norm(line):
    return ansi.sub('', line).strip()


lines = [re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '', line) for line in raw.splitlines()]
correspondence = []
for path in sorted(A.rglob('*.log')):
    rel = path.relative_to(A).as_posix()
    data = read(path).decode()
    marks = [i for i, line in enumerate(lines) if line == 'Log: /home/runner/work/_temp/nla-lean-tools/logs/' + rel]
    check(len(marks) == 1, 'unique raw job log start ' + rel)
    start = marks[0] + 1
    end = next(k for k in range(start, len(lines)) if
               (lines[k].startswith('Running ') and k + 1 < len(lines) and lines[k + 1].startswith('Log: '))
               or lines[k].startswith('PASS: fresh Comparator run') or lines[k].startswith('Tools built;'))
    actual = [norm(s) for s in lines[start:end] if norm(s)]
    payload = [norm(s) for s in data.splitlines()[1:] if norm(s) and not s.startswith('EXIT_STATUS=')]
    check(actual == payload, 'complete normalized raw job payload equality ' + rel)
    correspondence.append({'path': rel, 'sha256': sha(data.encode()), 'payload_lines': len(payload), 'actual_job_lines': [start + 1, end], 'exit_code': int(re.search(r'^EXIT_STATUS=(\d+)$', data, re.M)[1]), 'command': data.splitlines()[0]})
zpath = P / ('lean-' + PROBLEM + '.zip')
zdata = read(zpath)
check(sha(zdata) == CFG['zip_sha256'], 'expected retained ZIP digest')
with zipfile.ZipFile(zpath) as z:
    members = z.namelist()
    check(len(members) == len(set(members)) == 13, '13 unique ZIP members')
    check(set(members) == {p.relative_to(A).as_posix() for p in A.rglob('*') if p.is_file()}, 'exact ZIP and extracted member set')
    for name in members:
        check(not Path(name).is_absolute() and '..' not in Path(name).parts and z.read(name) == read(A / name), 'exact safe ZIP member bytes ' + name)
check(artifacts['total_count'] == 1, 'one artifact returned')
artifact = artifacts['artifacts'][0]
check(artifact['id'] == CFG['artifact'] and artifact['name'] == 'lean-' + PROBLEM and artifact['digest'] == 'sha256:' + sha(zdata) and not artifact['expired'], 'API artifact identity and digest')
check(artifact['workflow_run']['id'] == run['id'] and artifact['workflow_run']['head_sha'] == HEAD, 'artifact workflow/commit binding')
check(f'SHA256 digest of uploaded artifact zip is {sha(zdata)}' in raw and str(CFG['artifact']) in raw, 'actual raw upload artifact digest and ID')
legacy = js(P / 'ROOT-AUDIT.json')
read(P.parent.parent / 'audit_canonical_runtime.py')
check(legacy['actual_checkout'] == HEAD and legacy['exports'] == names and legacy['bound_inputs'] == len(inputs), 'prior generic audit corroborates independent result')
summary = {
    'reviewer': '/root/sf_ra_runtime_referee',
    'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': 'APPROVED: exact retained canonical Linux runtime evidence only',
    'scope': 'Independent nonauthor audit of authenticated retained execution evidence; no new execution and no new complete mathematical source review.',
    'run_id': run['id'], 'job_id': job['id'], 'literal_commit': HEAD, 'problem': PROBLEM, 'project': REL,
    'passed_assertions': len(checks), 'external_bindings': len(bindings),
    'project_inputs_matching_literal_Git_and_receipt_and_worktree': len(inputs),
    'accepted_source_bytes_preserved': len(math), 'final_import_closure': len(closure),
    'all_final_local_modules_freshly_built': sorted(built), 'canonical_Solution_freshly_built': True,
    'exact_exports': names, 'standard_three_axiom_reports': len(prints),
    'frozen_originals': len(frozen), 'active_frozen_unchanged': len(frozen) - 1,
    'only_active_configuration_transition': 'Lake default target Challenge to Solution and Solution library registration; original retained exactly.',
    'dependent_package_pins': pins, 'tool_receipt': tool, 'source_lock_sha256': lockhash,
    'shared_checker_unchanged_from': TRUSTED, 'shared_checker_sha256': shared_hashes,
    'actual_kernel_and_Comparator_accept': True, 'actual_negative_sorry_and_native_reject': True,
    'actual_three_kernel_and_five_Comparator_controls_pass': True,
    'actual_nonroot_build_and_export_sandbox_controls_pass': True,
    'all_twelve_complete_logs_read': True, 'single_project_selection': PROBLEM,
    'separate_checker_controls_job': 'Skipped on unchanged-harness push; per-proof controls actually ran in verify job.',
    'raw_log_correspondence': correspondence,
    'raw_log_normalization': 'Remove GitHub timestamps, ANSI display escapes, blank lines, first artifact command line and final EXIT_STATUS footer. Complete remaining payload must equal contiguous job block.',
    'artifact_id': artifact['id'], 'artifact_sha256': sha(zdata), 'zip_members_byte_identical': 13,
    'retained_source_review_manifests': preserved_reviews,
    'prior_helper_scope': 'Existing ROOT-AUDIT and helper hash-bound as corroboration. Its hardcoded /root label is not this reviewer identity. This reviewer did not rerun the helper.',
    'no_new_Lean_Lake_Comparator_cache_run': True, 'no_Git_mutation_source_edit_publication_or_count_action': True,
    'limitations': [
        'Relies on the supplied previously authenticated GitHub retrieval; this reviewer did not independently re-fetch remote metadata.',
        'Audit is not a new Lean/Comparator execution, official Tau Ceti review, human review, or guarantee of checker infallibility.',
        'Full mathematical fidelity and reviewer authorship scopes remain in the separate sealed source reviews, preserved by byte identity here.',
        'Acceptance binds this literal proof commit only. Later publication commits and upstream merge checkouts require their own applicable exact-source/runtime checks.'
    ]
}
for name, value in [
    ('CHECKS.json', summary), ('ASSERTIONS.json', checks), ('SOURCE-BINDINGS.json', bindings),
    ('GIT-INPUTS.json', {'commit': HEAD, 'project': REL, 'sha256': gitmap})
]:
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=name in ['SOURCE-BINDINGS.json', 'GIT-INPUTS.json']) + '\n')
print(json.dumps({'passed': True, 'assertions': len(checks), 'external_bindings': len(bindings), 'inputs': len(inputs), 'exports': len(names), 'source_count': len(math), 'final_closure': len(closure), 'logs_matched': len(correspondence), 'zip_members': 13}))

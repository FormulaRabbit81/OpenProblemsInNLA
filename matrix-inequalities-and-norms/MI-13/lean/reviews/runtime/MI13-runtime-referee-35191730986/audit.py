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


blob_cache = {}

def blob(path):
    if path in blob_cache:
        return blob_cache[path]
    data = git('show', HEAD + ':' + REL + '/' + path)
    gitmap[path] = sha(data)
    blob_cache[path] = data
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
check(len(config['permitted_axioms']) == 3 and set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'} and config['definition_names'] == [], 'standard three axioms and no definition holes')

B = Path('/private/tmp/nla-lean-next-20260915')
proof_workspace = B / 'next-proofs/MI-13'
freeze = json.loads(blob('STATEMENT-FREEZE.json'))
frozen = freeze['frozen_files']
check(len(frozen) == 13, 'exact thirteen frozen inputs')
for path, digest in frozen.items():
    check(sha(read(proof_workspace / path)) == digest, 'original frozen file preserved ' + path)
    if path != 'lakefile.toml':
        check(inputs[path] == digest, 'active frozen file unchanged ' + path)
oldlake = blob('statement-history/frozen-handoff/lakefile.toml')
check(sha(oldlake) == frozen['lakefile.toml'], 'literal retained frozen Lake file')
check(oldlake.replace(b'defaultTargets = ["Challenge"]', b'defaultTargets = ["Solution"]') +
      b'\n[[lean_lib]]\nname = "Solution"\n' == blob('lakefile.toml'), 'only Lake registration and default changed')
local = json.loads(blob('verification/LOCAL-COMPLETE.json'))
math = json.loads(blob('ACTIVE-SOURCE-MANIFEST.json'))['source_sha256']
check(math == local['sources'] and len(math) == 22, 'runtime package exactly local53 accepted 22 sources')
for path, digest in math.items():
    check(inputs[path] == digest and sha(read(proof_workspace / path)) == digest, 'exact local proof origin ' + path)
check({p for p in inputs if p.endswith('.lean')} == set(math) | {'Challenge.lean'}, 'only 23 active Lean inputs')
check(not any(Path(p).suffix in ['.olean', '.ilean', '.o', '.a', '.so', '.dylib'] for p in inputs), 'no compiled artifacts tracked')
manifest = json.loads(blob('lake-manifest.json'))
pins = {x['name']: x['rev'] for x in manifest['packages']}
check(len(pins) == 10 and pins == {x['name']: x['rev'] for x in js(proof_workspace / 'lake-manifest.json')['packages']}, 'ten exact frozen dependency pins')
check(sha(read(local['receipt'])) == local['receipt_sha256'] == 'a5027742b5bbd84bcc40f077696d3ba203b6f4220c33608cd89dd4ed52448711', 'actual final local53 receipt retained')

# Continue the exact prior package approval through the separately recorded review/status addition.
prior_rel = 'verification/packaging/before-package-review-acceptance/PACKAGE-MANIFEST.json'
check(inputs[prior_rel] == '95ac5a2fe203bb712cc29679e867aefdcc5679fceb0d9cceefba39e07e890579', 'previously approved package manifest')
before = json.loads(blob(prior_rel))['files']
transition = json.loads(blob('verification/packaging/PACKAGE-REVIEW-ACCEPTANCE-TRANSITION.json'))
check(transition['before_manifest_sha256'] == inputs[prior_rel] and transition['removed'] == [], 'metadata transition starts at approved package')
check(set(transition['changed']) == {'STATE.json','formalization.yaml','README.md','reviews/INDEX.json'}, 'four metadata files only')
for path, digest in before.items():
    if path in transition['changed']:
        change = transition['changed'][path]
        check(digest == change['before'] and inputs[path] == change['after'], 'exact metadata-only continuation ' + path)
    else:
        check(inputs[path] == digest, 'approved package payload unchanged ' + path)
for path, digest in transition['added'].items():
    check(path not in before and inputs[path] == digest, 'exact recorded package addition ' + path)
check(set(inputs) == set(before) | set(transition['added']) | {'PACKAGE-MANIFEST.json','verification/packaging/PACKAGE-REVIEW-ACCEPTANCE-TRANSITION.json'}, 'no unrecorded package transition paths')
package_manifest = json.loads(blob('PACKAGE-MANIFEST.json'))['files']
check(package_manifest == {p:h for p,h in inputs.items() if p != 'PACKAGE-MANIFEST.json'}, 'exact current package manifest')

preserved_reviews = {}
def authenticate_private_packet(name, expected_manifest):
    directory = B / 'reviews' / name
    check(sha(read(directory / 'MANIFEST.json')) == expected_manifest, 'immutable original review manifest ' + name)
    manifest_object = js(directory / 'MANIFEST.json')
    inventory = manifest_object.get('files', manifest_object.get('payloads', manifest_object))
    check(set(inventory) == {p.relative_to(directory).as_posix() for p in directory.rglob('*') if p.is_file() and p != directory/'MANIFEST.json'}, 'original review complete inventory ' + name)
    for path, value in inventory.items():
        digest = value['sha256'] if isinstance(value, dict) else value
        check(sha(read(directory / path)) == digest, 'original sealed review payload ' + name + '/' + path)
    preserved_reviews[name] = expected_manifest
    return directory, inventory

review_index = json.loads(blob('reviews/INDEX.json'))
check(review_index['two_full_nonauthor_source_reviews_accepted_by_root'] is True, 'two separate complete source approvals retained')
for item in review_index['reports']:
    check(inputs[item['report']] == item['report_sha256'], 'literal complete source report ' + item['report'])
    directory = Path(item['report']).parent.as_posix()
    check(inputs[directory+'/MANIFEST.json'] == item['original_manifest_sha256'], 'unchanged source review original manifest')
    authenticate_private_packet(Path(directory).name, item['original_manifest_sha256'])
first = json.loads(blob('reviews/final/MI13-full-referee1-20260917/SOURCE-MAP.json'))['files']
second = json.loads(blob('reviews/final/MI13-full-referee2-20260917/SOURCE-FINAL53-BINDINGS.json'))['bindings']
second_map = {Path(x['source']).relative_to(proof_workspace).as_posix():x['sha256'] for x in second}
check(set(second_map)-set(math) == {'STATEMENT-FREEZE.json'} and second_map['STATEMENT-FREEZE.json'] == inputs['STATEMENT-FREEZE.json'], 'second review additionally binds exact statement freeze')
second_map.pop('STATEMENT-FREEZE.json')
check(first == second_map == math, 'both complete source reviews bind exactly these 22 runtime sources')
pkg = review_index['package_review'];pkgdir = Path(pkg['report']).parent.as_posix()
check(inputs[pkg['report']] == pkg['report_sha256'] and inputs[pkgdir+'/MANIFEST.json'] == pkg['manifest_sha256'], 'retained package approval identity')
pkgprivate, pkgfiles = authenticate_private_packet(Path(pkgdir).name, pkg['manifest_sha256'])
for path, value in pkgfiles.items():
    digest = value['sha256'] if isinstance(value, dict) else value
    check(inputs[pkgdir+'/'+path] == digest, 'byte-identical retained package review '+path)
retained = json.loads(blob('reviews/RETAINED-PATHS.json'))
omitted = json.loads(blob('reviews/OMITTED-OUTPUTS.json'))
check(len(retained) == 653 and len(omitted) == 22, 'explicit public source-review retention and binary omission counts')
for item in retained:
    check(inputs[item['path']] == item['sha256'] == sha(read(item['original_path'])), 'retained review source correspondence ' + item['path'])
for item in omitted:
    check(item['intended_path'] not in inputs and item['original_path'].endswith('.olean') and
          sha(read(item['original_path'])) == item['sha256'], 'explicitly omitted private output ' + item['intended_path'])
for name in ['MI13-full-referee1-20260917','MI13-full-referee2-20260917']:
    private = B/'reviews'/name
    originals = {str(p) for p in private.rglob('*') if p.is_file()}
    mapped = {x['original_path'] for x in retained+omitted if Path(x['original_path']).is_relative_to(private)}
    check(originals == mapped, 'all original review paths retained or explicitly omitted '+name)
standards = {p:h for p,h in inputs.items() if p.startswith('sources/standards/')}
for path, digest in standards.items():
    check(before[path] == digest, 'unchanged pinned guidance and checker documentation '+path)
check(sha(blob('sources/standards/repository-checker-source-lock.json')) == lockhash, 'pinned project checker lock equals actual runtime lock')

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
check('have hhalf : (0 : ℝ) ≤ 1 / 2 := le_of_lt half_certificate.1' in blob('NLA/MI13/ElementaryBounds.lean').decode()
      and 'mul_le_mul_of_nonneg_left hsum hhalf' in blob('NLA/MI13/ElementaryBounds.lean').decode(), 'half certificate consumer retained')
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
check(all(len(p[1].split(', ')) == 3 and set(p[1].split(', ')) == set(config['permitted_axioms']) for p in prints), 'all Solution reports contain exactly standard three axioms')
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

check('warning:' not in comp[comp.index('Building Solution'):], 'no Solution closure warnings')
all_axioms = re.findall(r"'(NLA\.[\w.]+)' depends on axioms: \[([^\]]*)\]", comp)
check(all(len(a.split(', ')) == 3 and set(a.split(', ')) == {'propext','Quot.sound','Classical.choice'} for _,a in all_axioms), 'every printed local and wrapper axiom set has exactly the standard three')
check(artifact['size_in_bytes'] == len(zdata), 'API archive byte count')
check(run['run_number'] == 173 and run['head_branch'] == 'codex/lean-mi13-verification', 'expected proof-candidate run branch and sequence')
check(len(fetch['archives']) == 1 and fetch['archives'][0]['id'] == artifact['id'] and
      fetch['archives'][0]['sha256'] == sha(zdata), 'authenticated fetch archive binding')
for fj in fetch['jobs']:
    jj = next(j for j in jobs['jobs'] if j['id'] == fj['id'])
    check(jj['name'] == fj['name'] and jj['conclusion'] == fj['conclusion'], 'fetched actual job identity '+str(jj['id']))
correction = js(P/'ROOT-AUDIT-HELPER-CORRECTION.json')
original_helper = read(B/'audit_canonical_runtime.py')
corrected_helper = read(B/'audit_canonical_runtime_axiom_set.py')
check(sha(original_helper) == correction['original_helper_sha256'] and sha(corrected_helper) == correction['corrected_helper_sha256'], 'root helper correction immutable source hashes')
check(original_helper.replace(b"assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']",
      b"assert len(config['permitted_axioms']) == 3 and set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}") == corrected_helper,
      'root helper changed only order-sensitive list check to exact three-element set')
legacy = js(P/'ROOT-AUDIT.json')
check(legacy['actual_checkout'] == HEAD and legacy['exports'] == names and legacy['bound_inputs'] == len(inputs)
      and legacy['auditor_sha256'] == sha(corrected_helper), 'root audit corroborates independently reconstructed result')
check(legacy['actual_job_log_sha256'] == sha(raw.encode()), 'root raw log hash corroborates retained bytes')
for name, digest in legacy['raw_logs_sha256'].items():
    check(sha(logs[name].encode()) == digest, 'root log hash corroborates '+name)
for path,digest in list(bindings.items()):
    check(sha(Path(path).read_bytes()) == digest, 'external bytes stable through audit '+path)

summary = {
 'reviewer':'/root/sf_ra_runtime_referee','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'verdict':'APPROVED: exact retained canonical Linux runtime evidence for MI-13 proof commit only',
 'scope':'Independent evidence audit, not a new compiler/Comparator execution or a repeated complete mathematical review.',
 'run_id':run['id'],'job_id':job['id'],'literal_commit':HEAD,'problem':PROBLEM,'project':REL,
 'passed_assertions':len(checks),'external_bindings':len(bindings),'tracked_project_inputs':len(inputs),
 'accepted_source_bytes_preserved':len(math),'active_Lean_files':23,'final_import_closure':len(closure),
 'all_final_local_modules_freshly_built':sorted(built),'canonical_Solution_freshly_built':True,
 'exact_exports':names,'standard_three_Solution_axiom_reports':len(prints),'all_printed_axiom_reports':len(all_axioms),
 'frozen_originals':13,'active_frozen_unchanged':12,
 'only_active_frozen_transition':'Register Solution Lake library and select it as default; original Lake file preserved.',
 'package_review_followup':{'added_recorded_payloads':len(transition['added']),'changed_metadata_files':sorted(transition['changed']),
                            'separate_transition_record':True,'before_manifest':inputs[prior_rel]},
 'source_review_copy_map':{'retained_payloads':len(retained),'explicit_omitted_private_outputs':len(omitted)},
 'dependent_package_pins':pins,'tool_receipt':tool,'source_lock_sha256':lockhash,
 'shared_checker_unchanged_from':TRUSTED,'shared_checker_sha256':shared_hashes,
 'actual_kernel_and_Comparator_accept':True,'actual_negative_sorry_and_native_reject':True,
 'actual_three_kernel_and_five_Comparator_controls_pass':True,'actual_nonroot_sandbox_modes':['build','export'],
 'all_twelve_complete_artifact_logs_read':True,'single_project_selection':PROBLEM,
 'separate_checker_controls_job':'Skipped on unchanged-harness push; per-proof controls actually ran in verify job.',
 'raw_log_correspondence':correspondence,
 'raw_log_normalization':'Remove GitHub timestamps, ANSI display escapes, blank lines, first artifact command line and final EXIT_STATUS footer; complete remaining payload equals contiguous raw job block.',
 'artifact_id':artifact['id'],'artifact_sha256':sha(zdata),'zip_members_byte_identical':13,
 'retained_review_manifests':preserved_reviews,'root_helper_scope':'Root helper execution is corroboration only; this referee did not execute either helper.',
 'fresh_Lean_Lake_Comparator_cache_execution_by_referee':False,'Git_used_read_only':True,
 'proof_or_worktree_mutation':False,'publication_or_count_action':False,
 'limitations':['No new remote fetch; relies on the retained authenticated GitHub retrieval.',
 'Runtime approval does not replace the separate full mathematical and statement reviews.',
 'No official Tau Ceti or external-human-peer-review claim, nor guarantee of checker infallibility.',
 'A later publication commit and upstream merge checkout require their applicable source/runtime gates.']}
for name,value in [('CHECKS.json',summary),('ASSERTIONS.json',checks),('SOURCE-BINDINGS.json',bindings),
                   ('GIT-INPUTS.json',{'commit':HEAD,'project':REL,'sha256':gitmap})]:
    (OUT/name).write_text(json.dumps(value,indent=2,sort_keys=name in ['SOURCE-BINDINGS.json','GIT-INPUTS.json'])+'\n')
print(json.dumps({'passed':True,'assertions':len(checks),'external_bindings':len(bindings),'inputs':len(inputs),
 'exports':len(names),'source_count':len(math),'final_closure':len(closure),'logs_matched':len(correspondence),'zip_members':13}))

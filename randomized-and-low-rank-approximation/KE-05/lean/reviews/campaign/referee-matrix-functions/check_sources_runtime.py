"""Independent KE-05 source and historical-run audit. No Lean/Lake execution."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, zipfile
import yaml, jsonschema

ROOT = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
B = Path('/tmp/nla-lean-next-20260915')
OUT = B / 'reviews/KE05-mf22-independent'
PREFLIGHT = B / 'elimination/KE05-preflight'
READ = PREFLIGHT / 'existing-fork/randomized-and-low-rank-approximation/KE-05/lean'
SUPPORT = B / 'reviews/KE05-ie13-continuation-existing/source'
D = B / 'overlap-runs/KE05-34927150695'
E = D / 'artifacts/lean-KE-05/verify-20260915T040230Z-3936'
PROJECT = 'randomized-and-low-rank-approximation/KE-05/lean'
TESTED = '9acd5d5c9ab91c5c0c07603b6b48c0cb7ede54e6'
PUBLISHED = '04f3f39beb69d77dbc4a8eadee70259eb89a591a'
UPSTREAM = 'ce47b5630bf3680d9211131c3a43825b022c139a'
ORIGINAL = 'deb549fa9ddd6b119e6c59016f268237e645dfa2'
ACCEPTED_CHECKER = 'ff6abf718126ceb23f933cf4f627f95104461fe8'

def sha(data): return hashlib.sha256(data).hexdigest()
def digest(p): return sha(p.read_bytes())
def load(p): return json.loads(p.read_text())
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT)
def dump(name, obj): (OUT / name).write_text(json.dumps(obj, indent=2) + '\n')
def blob(commit, path): return git('cat-file', 'blob', commit + ':' + path)
def tree(commit, path):
    result = {}
    for record in git('ls-tree', '-r', '-z', commit, '--', path).split(b'\0'):
        if not record: continue
        meta, name = record.split(b'\t', 1)
        mode, kind, oid = meta.decode().split()
        assert mode in {'100644', '100755'} and kind == 'blob'
        result[name.decode()[len(path) + 1:]] = {'mode': mode, 'object': oid}
    return result
def batch(objects):
    raw = subprocess.check_output(['git', 'cat-file', '--batch'], input=('\n'.join(objects) + '\n').encode(), cwd=ROOT)
    pos, data = 0, {}
    for item in objects:
        end = raw.index(b'\n', pos)
        header = raw[pos:end].decode().split()
        assert len(header) == 3 and header[1] == 'blob', (item, header)
        size = int(header[2]); start = end + 1
        value = raw[start:start + size]
        assert raw[start + size:start + size + 1] == b'\n'
        data[item] = value; pos = start + size + 1
    assert pos == len(raw)
    return data

OUT.mkdir(parents=True, exist_ok=True)
tested_tree, published_tree = tree(TESTED, PROJECT), tree(PUBLISHED, PROJECT)
receipt = load(E / 'result.json')
assert receipt['repository_commit'] == TESTED and receipt['project'] == PROJECT
assert receipt['result'] == 'comparator-accepted'
assert set(tested_tree) == set(published_tree) == set(receipt['input_sha256'])
assert len(tested_tree) == 93
objects = sorted({v['object'] for t in [tested_tree, published_tree] for v in t.values()})
data = batch(objects)
input_bindings = []
changed = []
for rel, entry in tested_tree.items():
    old = data[entry['object']]; new = data[published_tree[rel]['object']]
    assert sha(old) == receipt['input_sha256'][rel], rel
    if old != new: changed.append(rel)
    input_bindings.append({'path': rel, 'tested_blob': entry['object'], 'published_blob': published_tree[rel]['object'], 'tested_sha256': sha(old), 'published_sha256': sha(new), 'unchanged': old == new})
assert sorted(changed) == ['README.md', 'formalization.yaml']
dump('ALL-93-INPUT-BINDINGS.json', input_bindings)

lean_files = sorted([str(p.relative_to(READ)) for p in (READ / 'NLA/KE05').glob('*.lean')] + ['Challenge.lean', 'Solution.lean'])
assert len(lean_files) == 23
source_records = []
for rel in lean_files:
    content = (READ / rel).read_bytes()
    assert content == data[tested_tree[rel]['object']] == data[published_tree[rel]['object']] == (SUPPORT / rel).read_bytes(), rel
    source_records.append({'path': rel, 'sha256': sha(content), 'bytes': len(content), 'lines': len(content.splitlines()), 'Git_blob_at_both_revisions': tested_tree[rel]['object']})
dump('ALL-23-SOURCES.json', source_records)

canonical = []
for name in ['README.md', 'solution.md']:
    rel = 'randomized-and-low-rank-approximation/KE-05/' + name
    content = (PREFLIGHT / 'canonical' / name).read_bytes()
    assert content == blob(UPSTREAM, rel) == blob(ORIGINAL, rel)
    canonical.append({'path': rel, 'sha256': sha(content), 'upstream_commit': UPSTREAM, 'original_formalized_commit': ORIGINAL})
dump('CANONICAL-TARGET-BINDINGS.json', canonical)

def code_only(text):
    return re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', text, flags=re.S))
def headers(content):
    return {m.group(1): re.sub(r'\s+', ' ', m.group(2)).strip() for m in re.finditer(r'\btheorem\s+(\w+)\s*(.*?)\s*:=\s*by', code_only(content), re.S)}
challenge, solution = (READ / 'Challenge.lean').read_text(), (READ / 'Solution.lean').read_text()
hchallenge, hsolution = headers(challenge), headers(solution)
assert len(hchallenge) == 10 and hchallenge == hsolution
config = load(READ / 'comparator.json')
exports = config['theorem_names']
assert exports == ['NLA.KE05.' + name for name in hchallenge]
assert config['definition_names'] == [] and set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert config == receipt['config']
dump('ALL-10-HEADERS.json', hchallenge)

closure, todo = {}, ['Solution.lean']
while todo:
    rel = todo.pop()
    if rel in closure: continue
    txt = code_only((READ / rel).read_text())
    imports = re.findall(r'^import\s+(\S+)\s*$', txt, flags=re.M)
    assert not any(x == 'Challenge' for x in imports)
    assert not re.search(r'\b(?:sorry|axiom|native_decide|unsafe|implemented_by|run_tac)\b', txt), rel
    closure[rel] = imports
    for name in imports:
        if name.startswith('NLA.KE05.'):
            todo.append(name.replace('.', '/') + '.lean')
        else: assert name in {'Mathlib', 'LeanCert.Tactic.Verification'}, (rel, name)
assert len(closure) == 22 and set(closure) == set(lean_files) - {'Challenge.lean'}
assert re.findall(r'^#assert_trust kernel (\S+)$', solution, re.M) == exports
assert len(re.findall(r'\bsorry\b', code_only(challenge))) == 10
dump('ACTIVE-IMPORT-CLOSURE.json', closure)

freeze = load(SUPPORT / 'verification/statement-freeze.json')
assert len(freeze['files_sha256']) == 10
frozen_records = {}
for rel, expected in freeze['files_sha256'].items():
    content = data[published_tree[rel]['object']]
    if rel == 'lakefile.toml':
        amendment = load(SUPPORT / 'verification/build-config-revision.json')
        old = (SUPPORT / amendment['old_bytes']).read_bytes()
        assert sha(old) == expected == amendment['before_sha256']
        assert old + amendment['exact_added_text'].encode() == content
        assert sha(content) == amendment['after_sha256']
        frozen_records[rel] = {'status': 'only documented appended Solution library; default still Challenge', 'frozen_sha256': expected, 'published_sha256': sha(content)}
    else:
        assert sha(content) == expected, rel
        frozen_records[rel] = {'status': 'unchanged', 'sha256': expected}
for rel, expected in freeze['referees'].items(): assert sha(data[published_tree[rel]['object']]) == expected
assert 'defaultTargets = ["Challenge"]' in (READ / 'lakefile.toml').read_text()
dump('FROZEN-BOUNDARY.json', frozen_records)

metadata = yaml.safe_load((READ / 'formalization.yaml').read_text())
jsonschema.validate(metadata, json.loads(blob(TESTED, 'docs/lean/schema/v0.4.schema.json')))
assert metadata['project']['authors'] == ['Sidney Holden']
assert {r['declaration'] for r in metadata['status']['main_results']} == set(exports)
assert sha(data[published_tree['LICENSE']['object']]) == 'cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30'
assert set(changed).isdisjoint(set(lean_files) | {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'comparator.json', 'LICENSE'})

run, jobs, artifacts = load(D / 'run.json'), load(D / 'jobs.json'), load(D / 'artifacts.json')
assert run['id'] == 34927150695 and run['head_sha'] == TESTED and run['conclusion'] == 'success'
assert run['repository']['full_name'] == 'sidneyholden1/OpenProblemsInNLA'
job = next(j for j in jobs['jobs'] if j['id'] == 104247549056)
assert job['run_id'] == run['id'] and job['head_sha'] == TESTED and job['conclusion'] == 'success'
assert next(s for s in job['steps'] if s['name'] == 'Fresh sandboxed statement, axiom and kernel verification')['conclusion'] == 'success'
assert next(j for j in jobs['jobs'] if j['name'] == 'checker-controls')['conclusion'] == 'skipped'
artifact = artifacts['artifacts'][0]
zip_sha = digest(D / 'lean-KE-05.zip')
assert artifact['id'] == 10380179618 and artifact['digest'] == 'sha256:' + zip_sha
assert zip_sha == '6925d651c338b1ce7af48368af631e28e70a2cf047a5029db594b8aaae4da682'
assert artifact['workflow_run']['head_sha'] == TESTED
zip_members = []
with zipfile.ZipFile(D / 'lean-KE-05.zip') as z:
    for name in z.namelist():
        if name.endswith('/'): continue
        value = z.read(name)
        assert value == (D / 'artifacts/lean-KE-05' / name).read_bytes(), name
        zip_members.append({'path': name, 'sha256': sha(value)})
assert len(zip_members) == 13
dump('AUTHENTICATED-ARTIFACT-MEMBERS.json', zip_members)

raw = (D / 'job-104247549056.log').read_text()
raw_lines = set(re.sub(r'^\d{4}-\d\d-\d\dT[0-9:.]+Z ', '', s) for s in raw.splitlines())
assert TESTED in raw and zip_sha in raw and '10380179618' in raw
log_checks = {}
for path in sorted(E.glob('*.log')):
    text = path.read_text()
    expected_exit = 1 if path.name in {'negative-native.log', 'negative-sorry.log'} else 0
    assert text.rstrip().endswith('EXIT_STATUS=' + str(expected_exit)), path.name
    observed = [s for s in text.splitlines() if s.strip() and not s.startswith('$ ') and not s.startswith('EXIT_STATUS=')]
    unmatched = [s for s in observed if s not in raw_lines]
    assert not unmatched, (path.name, unmatched[:3])
    log_checks[path.name] = {'sha256': digest(path), 'expected_exit': expected_exit, 'actual_payload_lines_matched_to_raw_GitHub_job': len(observed)}
assert len(log_checks) == 9
comparator = (E / 'comparator.log').read_text()
assert 'Building Challenge' in comparator and 'Building Solution' in comparator
before, after = comparator.split('Building Solution', 1)
assert len(re.findall(r'warning: Challenge\.lean:.*declaration uses `sorry`', before)) == 10
assert 'declaration uses `sorry`' not in after and 'Illegal axiom' not in after
reports = dict(re.findall(r"'(NLA\.KE05\.[^']+)' depends on axioms: \[([^]]+)\]", after))
assert set(reports) == set(exports)
for name, names in reports.items(): assert set(names.split(', ')) == set(config['permitted_axioms']), (name, names)
for module in ['Challenge', 'Solution']:
    declaration_line = next(s for s in comparator.splitlines() if s.startswith('Exporting #[') and s.endswith(' from ' + module))
    assert re.findall(r'NLA\.KE05\.\w+', declaration_line) == exports
for rel in lean_files:
    assert 'Built ' + rel.removesuffix('.lean').replace('/', '.') + ' (' in comparator, rel
assert 'Lean default kernel accepts the solution' in after and 'Your solution is okay!' in after
assert "Illegal axiom detected: 'sorryAx'" in (E / 'negative-sorry.log').read_text()
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in (E / 'negative-native.log').read_text()
kernel = (E / 'kernel-controls.log').read_text()
for text in ['RETURN honest_with_inductives_and_quotients: accepted', 'RETURN invalid_raw_proof: rejected', 'RETURN quotient_postcheck_mismatch: rejected', 'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
    assert text in kernel
regressions = (E / 'comparator-controls.log').read_text()
for text in ['PASS simple_match: exit 0, expected 0', 'PASS simple_mismatch: exit 1, expected 1', 'PASS simple_axiom_issue: exit 1, expected 1', 'PASS simple_kind_mismatch: exit 1, expected 1', 'PASS type_mismatch: exit 1, expected 1', 'PASS: all five Comparator regressions']:
    assert text in regressions
sandbox = (E / 'sandbox.log').read_text()
assert re.findall(r'Sandbox UID: (\d+)', sandbox) == ['1001', '1001']
for text in ['PASS export .lake write-open: denied', 'PASS build .lake write: allowed', 'PASS outside .lake write-open: denied', 'PASS host loopback listener: unreachable', 'PASS AF_UNIX socket creation: denied', 'PASS nested namespace write attempt: rejected', 'Outer and export fixture contents unchanged']:
    assert text in sandbox
for name in ['unknown option', 'unexpected --rw', 'unexpected --rwx', 'relative --rwx']:
    assert 'NEGATIVE ' + name + ': exit=2' in sandbox

for rel in ['tools/lean', '.github/workflows/lean-verification.yml']:
    assert not git('diff', ACCEPTED_CHECKER, TESTED, '--', rel), rel
    assert not git('diff', TESTED, PUBLISHED, '--', rel), rel
lock = blob(TESTED, 'tools/lean/source-lock.json')
assert sha(lock) == receipt['source_lock_sha256'] == receipt['tool_receipt']['source_lock_sha256']
assert receipt['tool_receipt']['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert 'x86_64-unknown-linux-gnu' in receipt['tool_receipt']['lean_version']
assert receipt['tool_receipt']['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
deps = json.loads(data[tested_tree['lake-manifest.json']['object']])['packages']
assert len(deps) == 10
for dep in deps: assert dep['rev'] in (E / 'dependencies.log').read_text()
dump('HISTORICAL-LOG-CHECKS.json', log_checks)

checks = {
    'reviewer': '/root/mf22_publication_referee; independent nonimplementing AI agent',
    'reviewed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': 'approve complete original-target source and authenticated historical execution; fresh campaign run remains pending',
    'existing_formalization_author': 'Sidney Holden',
    'mathematical_author': 'George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology',
    'original_framework_and_conjecture': 'Nian Shao',
    'tested_commit': TESTED,
    'published_commit': PUBLISHED,
    'all_23_Lean_sources_read_and_bound_to_both_Git_commits': True,
    'source_lines': sum(item['lines'] for item in source_records),
    'source_bytes': sum(item['bytes'] for item in source_records),
    'active_import_closure_files': 22,
    'frozen_exports': 10,
    'all_10_export_headers_equal_Challenge': True,
    'definition_holes': [],
    'all_93_historical_receipt_inputs_bound_to_Git': True,
    'published_project_differences_from_tested': sorted(changed),
    'canonical_source_matches_original_formalized_revision': True,
    'frozen_boundary': '9 unchanged files; old Lakefile plus exactly documented Solution library registration reproduces current Lakefile',
    'LeanCert_use': '10 actually compiled #assert_trust kernel checks; exact proof requires no interval certificate',
    'permitted_actual_export_axioms': config['permitted_axioms'],
    'metadata_schema_valid': True,
    'license': 'Apache-2.0, unchanged',
    'historical_run': 34927150695,
    'historical_job': 104247549056,
    'artifact_id': 10380179618,
    'artifact_sha256': zip_sha,
    'receipt_sha256': digest(E / 'result.json'),
    'raw_job_sha256': digest(D / 'job-104247549056.log'),
    'raw_payload_lines_reconciled': sum(x['actual_payload_lines_matched_to_raw_GitHub_job'] for x in log_checks.values()),
    'whole_Solution_actual_build_default_kernel_Comparator_and_controls': 'PASS at tested historical commit',
    'separate_checker_controls_job': 'skipped; all required controls actually ran within successful project verification job',
    'no_blocking_mathematical_defect_found': True,
    'fresh_campaign_rerun_prerequisites': ['Preserve all reviewed mathematical/frozen/configuration bytes or explicitly reconcile a build-only default-target amendment.', 'Use lake build Solution explicitly, or change default target to Solution with prior bytes retained; plain current lake build selects Challenge.', 'Run the committed campaign candidate through the actual non-root Linux canonical harness, all 10 exports and every required project control, then authenticate exact source hashes and receipts.', 'Preserve Sidney Holden formalization authorship and Apache-2.0 license; distinguish George Stepaniants mathematical authorship and Nian Shao original framework.'],
    'local_Lean_Lake_cache_execution': False,
    'fresh_independent_checker_rerun': False,
    'edits_to_proof_or_publication_count_or_PR': False,
    'limits': 'Independent full-source reasoning and audit of fetched authenticated historical GitHub evidence. No claim of a new checker execution, human peer review, official Tau Ceti endorsement or tool/platform infallibility.'
}
dump('CHECKS.json', checks)
print(json.dumps({'verdict': checks['verdict'], 'Lean_sources': len(source_records), 'historical_inputs': len(input_bindings), 'raw_payload_lines': checks['raw_payload_lines_reconciled'], 'CHECKS_sha256': digest(OUT / 'CHECKS.json')}, indent=2))

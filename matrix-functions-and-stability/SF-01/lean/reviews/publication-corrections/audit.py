"""Read-only bounded continuation of SF01 publication corrections.

No proof/metadata/PDF/catalog/Git mutation. Only this review directory is written.
The original runtime and publication reviews remain separately sealed.
"""
from pathlib import Path
import datetime
import difflib
import hashlib
import json
import os
import subprocess

OUT = Path(__file__).resolve().parent
B = OUT.parent.parent
P = B / 'SF01-publication-private-35175258802'
PRIOR = B / 'reviews/SF01-publication-referee-35175258802'
W = Path('/private/tmp/nla-lean-next-sf01-worktree')
REL = 'matrix-functions-and-stability/SF-01/lean'
HEAD = '3312b0795873cfecade03fa421a5433651d47674'
record_path = B / 'SF01-PUBLICATION-CORRECTIONS.json'
bindings = {}
checks = []
diffs = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    path = Path(path)
    data = path.read_bytes()
    bindings[str(path)] = sha(data)
    return data


def js(path):
    return json.loads(read(path))


def check(value, label):
    if not value:
        raise AssertionError(label)
    checks.append(label)


def diff(old, new, label):
    diffs.extend(difflib.unified_diff(old.decode().splitlines(True), new.decode().splitlines(True), fromfile='sealed-draft/' + label, tofile='corrected/' + label))


check(subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(W), 'rev-parse', 'HEAD'], text=True).strip() == HEAD, 'worktree still on immutable verified proof HEAD')
record_data = read(record_path)
check(sha(record_data) == '71e74b0e1e4c7f6f70f02265e2efa5ae9c6f577d91347bd4d0f885dca725d7d0', 'exact root correction record')
record = json.loads(record_data)
check(sha(read(P / 'MANIFEST.json')) == record['original_overlay_manifest_sha256'] == '054a69e207cd88e37f9ca535b30cf202e20860c016cb89991345d80b8e5791c8', 'original overlay seal retained')
check(sha(read(PRIOR / 'MANIFEST.json')) == record['independent_conditional_review_sha256'] == 'db308d422a6a5884dd080dc953f8d64e740e4ff299506052c7439b550ed661c8', 'conditional review seal retained')
proposal = js(P / 'MANIFEST.json')
for path, digest in proposal['files'].items():
    check(sha(read(P / path)) == digest, 'original sealed proposal file ' + path)
prior_manifest = js(PRIOR / 'MANIFEST.json')
for path, digest in prior_manifest['files'].items():
    check(sha(read(PRIOR / path)) == digest, 'original conditional review payload ' + path)
t = js(P / 'TRANSITION.json')
index_path = REL + '/reviews/INDEX.json'
corrections = {x['path']: x for x in record['requested_corrections']}
expected_paths = {index_path, 'RESOLVED.md', REL + '/formalization.yaml', REL + '/verification/linux-35175258802/README.md'}
check(set(corrections) == expected_paths, 'exact four requested worktree correction paths')
spacing_replacements = {
    'RESOLVED.md': [('complete24-target', 'complete 24-target')],
    REL + '/formalization.yaml': [('contains24', 'contains 24'), ('All24', 'All 24')],
    REL + '/verification/linux-35175258802/README.md': [('all271', 'all 271'), ('all24', 'all 24'), ('UID1001', 'UID 1001')]
}
for path, pairs in spacing_replacements.items():
    old = read(P / 'overlay' / path)
    new = read(W / path)
    expected = old.decode()
    for before, after in pairs:
        check(expected.count(before) == 1, 'single requested spacing occurrence ' + path + ' ' + before)
        expected = expected.replace(before, after)
    check(expected.encode() == new, 'only requested spaces changed ' + path)
    check(sha(old) == corrections[path]['before_sha256'] and sha(new) == corrections[path]['after_sha256'], 'recorded spacing before/after hashes ' + path)
    diff(old, new, path)
old_index_bytes = read(P / 'overlay' / index_path)
old_index = json.loads(old_index_bytes)
new_index_bytes = read(W / index_path)
new_index = json.loads(new_index_bytes)
intermediate = dict(old_index)
intermediate['canonical_runtime'] = 'Accepted actual non-root Linux run 35175258802 at 3312b0795873cfecade03fa421a5433651d47674; later publication and upstream executions remain separate gates.'
intermediate['current_complete_source_approval'] = 'Two nonauthor reviews accepted; exact disclosures retained in full reports. The actual canonical run 35175258802 and independent runtime audit are accepted. Later publication and upstream executions remain separate gates.'
intermediate_bytes = (json.dumps(intermediate, indent=2) + '\n').encode()
check(sha(old_index_bytes) == corrections[index_path]['before_sha256'], 'original index correction hash')
check(sha(intermediate_bytes) == corrections[index_path]['after_sha256'], 'recorded after-index hash identifies precise intermediate two-field correction')
expected_index = dict(intermediate)
expected_index['publication_overlay_reviews'] = [{
    'path': 'reviews/publication-overlay/REVIEW.md',
    'manifest_sha256': record['independent_conditional_review_sha256'],
    'scope': 'Independent conditional publication review; bounded requested corrections separately recorded and awaiting follow-through'
}]
check(new_index == expected_index and new_index_bytes == (json.dumps(expected_index, indent=2) + '\n').encode(), 'final index contains only the two corrected current fields plus scoped publication review link')
diff(old_index_bytes, new_index_bytes, index_path)
for path, digest in t['overlay'].items():
    check(sha(read(P / 'overlay' / path)) == digest, 'sealed overlay source still exact ' + path)
    if path not in corrections:
        check(sha(read(W / path)) == digest, 'all other applied overlay bytes unchanged ' + path)
allowed_old_project_changes = {'README.md', 'formalization.yaml', 'PUBLICATION-EVIDENCE.json', 'reviews/INDEX.json'}
for path, digest in t['protected_original_inputs'].items():
    if path not in allowed_old_project_changes:
        check(sha(read(W / REL / path)) == digest, 'protected original input unchanged ' + path)
check(len(t['protected_original_inputs']) == 271 and len(t['protected_math_files']) == 37, 'accepted original input and mathematical source inventories complete')
for path, digest in t['protected_math_files'].items():
    check(sha(read(W / REL / path)) == digest, 'all mathematical bytes unchanged ' + path)
pr_old = read(P / 'PR-BODY.md')
pr_new = read(B / 'SF01-PR-BODY.md')
expected_pr = pr_old.decode()
for before, after in [('Theorem1', 'Theorem 1'), ('all271', 'all 271'), ('all24', 'all 24'), ('Lean4.33.1', 'Lean 4.33.1'), ('Mathlib0df', 'Mathlib 0df'), ('LeanCert621', 'LeanCert 621')]:
    check(expected_pr.count(before) == 1, 'single planned PR spacing occurrence ' + before)
    expected_pr = expected_pr.replace(before, after)
check(pr_new == expected_pr.encode() and sha(pr_new) == record['PR_body_sha256'], 'only required PR body spacing changed; exact hash retained')
check('DRAFT:' in pr_new.decode() and 'Replace this paragraph with measured results before posting.' in pr_new.decode(), 'planned PR checklist remains explicit pending gate before posting')
diff(pr_old, pr_new, 'PR-BODY.md')
# Additional evidence is enumerated and checked; it is not silently attributed
# to the original 36-path proposal.
additional = {}
for path in PRIOR.iterdir():
    if path.is_file():
        target = W / REL / 'reviews/publication-overlay' / path.name
        check(read(target) == read(path), 'unchanged attached conditional publication review ' + path.name)
        additional[target.relative_to(W).as_posix()] = sha(read(target))
snapshot_map = {
    'README.md': 'matrix-functions-and-stability/SF-01/README.md',
    'lean/README.md': REL + '/README.md',
    'lean/formalization.yaml': REL + '/formalization.yaml',
    'lean/PUBLICATION-EVIDENCE.json': REL + '/PUBLICATION-EVIDENCE.json',
    'lean/reviews/INDEX.json': REL + '/reviews/INDEX.json'
}
for target, original in snapshot_map.items():
    path = W / REL / 'verification/publication/before' / target
    check(read(path) == read(P / 'before' / original), 'exact before-document snapshot ' + target)
    additional[path.relative_to(W).as_posix()] = sha(read(path))
applied = W / REL / 'verification/publication/ROOT-APPLIED.json'
check(read(applied) == record_data, 'ROOT-APPLIED exact correction record copy')
additional[applied.relative_to(W).as_posix()] = sha(read(applied))
pdf = W / 'matrix-functions-and-stability/SF-01/solution.pdf'
pdf_bytes = read(pdf)
check(pdf_bytes.startswith(b'%PDF-') and sha(pdf_bytes) == record['solution_PDF_sha256'], 'PDF bytes match root render/visual record; no independent visual claim')
additional[pdf.relative_to(W).as_posix()] = sha(pdf_bytes)
check(read(W / 'matrix-functions-and-stability/SF-01/solution.tex') == read(P / 'overlay/matrix-functions-and-stability/SF-01/solution.tex'), 'rendered solution TeX source unchanged')
# Run the unchanged repository validator in the restored private PyYAML env.
validator = W / 'tools/lean/validate_manifest.py'
schema = W / 'docs/lean/schema/v0.4.schema.json'
read(validator); read(schema)
argv = ['/Users/georgestepaniants/miniforge3/bin/python', '-B', str(validator), str(W / REL)]
env = dict(os.environ)
env['PYTHONPATH'] = '/tmp/nla-publication-python-20260917'
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
validation = subprocess.run(argv, env=env, capture_output=True)
end = datetime.datetime.now(datetime.timezone.utc).isoformat()
validation_bytes = validation.stdout + validation.stderr
(OUT / 'MANIFEST-VALIDATION.log').write_bytes(validation_bytes)
check(validation.returncode == 0 and b'Manifest schema and comparator coverage: PASS (24 declarations)' in validation_bytes, 'actual unchanged repository metadata validator passes all24 declarations')
validation_receipt = {'argv': argv, 'PYTHONPATH': env['PYTHONPATH'], 'started_at_utc': start, 'ended_at_utc': end, 'exit_code': validation.returncode, 'log_sha256': sha(validation_bytes), 'validator_sha256': sha(read(validator)), 'schema_sha256': sha(read(schema))}
(OUT / 'MANIFEST-VALIDATION.json').write_text(json.dumps(validation_receipt, indent=2) + '\n')
summary = {
    'reviewer': '/root/sf_ra_runtime_referee', 'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': 'APPROVED: the exact requested SF01 publication corrections and explicitly enumerated evidence additions; no requested source correction remains.',
    'scope': 'Bounded independent publication correction follow-through; no new full proof review, compiler, Lean, Comparator, PDF visual, catalog/ID, publication or upstream execution claim.',
    'proof_HEAD': HEAD, 'root_correction_record_sha256': sha(record_data),
    'prior_conditional_review_manifest_sha256': record['independent_conditional_review_sha256'],
    'passed_assertions': len(checks), 'external_bindings': len(bindings),
    'requested_worktree_correction_paths': sorted(corrections),
    'intermediate_index_sha256': sha(intermediate_bytes), 'final_index_sha256': sha(new_index_bytes),
    'exact_original_overlay_paths': 36, 'protected_original_input_inventory': 271, 'unchanged_math_sources': 37,
    'additional_root_evidence_files': additional,
    'repository_metadata_validator': validation_receipt,
    'PDF_scope': 'Root reports solution PDF rendered twice and both pages visually inspected. This referee checked unchanged TeX and PDF digest only, and did not independently render or visually inspect either PDF.',
    'remaining_separate_gates': ['Replace planned PR draft checklist with measured completed results before posting', 'Root canonical PDF and catalog/permanent-ID gates and their separate evidence', 'Actual exact publication-commit and upstream PR execution'],
    'no_worktree_source_Git_state_publication_count_mutation': True
}
for name, data in [('CHECKS.json', summary), ('ASSERTIONS.json', checks), ('SOURCE-BINDINGS.json', bindings)]:
    (OUT / name).write_text(json.dumps(data, indent=2, sort_keys=name == 'SOURCE-BINDINGS.json') + '\n')
(OUT / 'CORRECTIONS.diff').write_text(''.join(diffs))
print(json.dumps({'passed': True, 'assertions': len(checks), 'external_bindings': len(bindings), 'original_overlay_paths': 36, 'protected_input_inventory': 271, 'unchanged_math_sources': 37, 'additional_evidence_files': len(additional), 'repository_validator': 'PASS24', 'remaining_requested_corrections': 0}))

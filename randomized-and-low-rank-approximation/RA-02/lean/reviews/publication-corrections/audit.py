"""Read-only bounded continuation of the sealed RA02 publication review.

Only this review directory is written. No Git, compiler, PDF rendering,
publication, catalog, metadata or worktree mutation is performed.
"""
from pathlib import Path
import datetime
import difflib
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
B = OUT.parent.parent
P = B / 'RA02-publication-private-35175272827'
PRIOR = B / 'reviews/RA02-publication-referee-35175272827'
W = Path('/private/tmp/nla-lean-next-ra02-worktree')
BASE = 'randomized-and-low-rank-approximation/RA-02'
REL = BASE + '/lean'
QA = B / 'RA02-publication-pdf-qa'
record_path = B / 'RA02-PUBLICATION-CORRECTIONS.json'
bindings = {}
checks = []
diffs = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    path = Path(path).resolve()
    data = path.read_bytes()
    bindings[str(path)] = sha(data)
    return data


def js(path):
    return json.loads(read(path))


def check(value, label):
    if not value:
        raise AssertionError(label)
    checks.append(label)


def difference(old, new, label):
    value = ''.join(difflib.unified_diff(old.decode().splitlines(True), new.decode().splitlines(True), fromfile='sealed/' + label, tofile='applied/' + label))
    diffs.append(value)
    return value


def manifest(folder, expected):
    data = read(folder / 'MANIFEST.json')
    check(sha(data) == expected, 'exact retained manifest ' + str(folder))
    value = json.loads(data)
    for path, digest in value['files'].items():
        check(sha(read(folder / path)) == digest, 'sealed payload unchanged ' + str(folder / path))
    return value


record_data = read(record_path)
check(sha(record_data) == 'e6a07bca8fc8469b5313711813f16d8b1f1ab059d3afa963544163453ad8ee93', 'exact root correction transition record')
record = json.loads(record_data)
proposal = manifest(P, '2386eb322ef6467f32c034f41f7fe11e6971ada5e2b00ec5c4d4b83b60b429df')
prior = manifest(PRIOR, '242826d3c16b49a19e868a5231043629c8d322241199c9c27d60940efa7b7ef1')
check(record['overlay_manifest_sha256'] == sha(read(P / 'MANIFEST.json')) and record['conditional_review_manifest_sha256'] == sha(read(PRIOR / 'MANIFEST.json')), 'root record binds the exact original proposal and conditional review')
t = js(P / 'TRANSITION.json')
check(len(t['overlay']) == 44 and len(t['protected_original_inputs']) == 220 and len(t['protected_math_files']) == 35, 'exact original 44-path proposal and protected inventories')

# Reauthenticate the old review's bindings. Seven live documentation paths have
# advanced by this explicit transition; authenticate their retained old bytes
# and their new overlay bytes separately rather than pretend they are unchanged.
old_bindings = js(PRIOR / 'SOURCE-BINDINGS.json')
transitioned = {}
for path, digest in old_bindings.items():
    source = Path(path)
    if source.is_relative_to(W) and source.relative_to(W).as_posix() in t['before'] and t['before'][source.relative_to(W).as_posix()] is not None:
        rel = source.relative_to(W).as_posix()
        check(sha(read(P / 'before' / rel)) == digest == t['before'][rel], 'old live documentation binding preserved in exact before snapshot ' + rel)
        transitioned[rel] = digest
    else:
        check(sha(read(source)) == digest, 'prior review unchanged binding ' + path)
check(len(old_bindings) == 687 and len(transitioned) == 7, '680 unchanged old bindings and seven explicit documentation transitions')

note_path = BASE + '/solution.tex'
index_path = REL + '/reviews/INDEX.json'
canonical_path = BASE + '/problem.tex'
canonical_readme_path = BASE + '/README.md'
excluded_canonical = json.loads((OUT / 'EXCLUDED-CANONICAL-TRANSITION.json').read_bytes())
check(sha((OUT / 'EXCLUDED-CANONICAL-SNAPSHOT.tex').read_bytes()) == excluded_canonical['observed_sha256'], 'concurrent canonical-render observation snapshot is exact; not an approval of that separate transition')
check(excluded_canonical['sealed_overlay_sha256'] == t['overlay'][canonical_path], 'separate canonical transition starts from the reviewed proposal TeX')
check(sha((OUT / 'EXCLUDED-CANONICAL-README.md').read_bytes()) == excluded_canonical['README_observed_sha256'] and excluded_canonical['README_sealed_overlay_sha256'] == t['overlay'][canonical_readme_path], 'concurrent canonical README date transition is separately identified with an exact observation snapshot')
check((OUT / 'EXCLUDED-CANONICAL-README.md').read_bytes() == read(P / 'overlay' / canonical_readme_path).replace(b'**Last checked:** 2026-09-17', b'**Last checked:** 2026-09-11', 1), 'observed separate README correction restores only the original literature date')
for path, digest in t['overlay'].items():
    check(sha(read(P / 'overlay' / path)) == digest, 'original overlay source unchanged ' + path)
    if path not in {note_path, index_path, canonical_path, canonical_readme_path}:
        check(sha(read(W / path)) == digest, 'all other applied overlay bytes unchanged ' + path)
for path, digest in t['protected_original_inputs'].items():
    if path not in t['changed_original_project_documents']:
        check(sha(read(W / REL / path)) == digest, 'original non-document input unchanged ' + path)
for path, digest in t['protected_math_files'].items():
    check(sha(read(W / REL / path)) == digest, 'all accepted mathematical bytes unchanged ' + path)

corrections = js(PRIOR / 'REQUIRED-CORRECTIONS.json')
check(len(corrections) == 1 and corrections[0]['path'] == 'PR-BODY.md', 'exact one original requested correction')
old_pr = read(P / 'PR-BODY.md')
new_pr = read(B / 'RA02-PR-BODY.md')
correction = corrections[0]
check(sha(old_pr) == correction['before_sha256'] and old_pr.decode().count(correction['old_text']) == 1, 'required PR clarification original bytes and unique occurrence')
check(new_pr.decode() == old_pr.decode().replace(correction['old_text'], correction['required_replacement'], 1), 'only requested planned-PR attribution clarification applied')
check(sha(new_pr) == record['PR_body_sha256'], 'root correction record exact final planned PR body')
check('DRAFT FOR THE COORDINATOR:' in new_pr.decode() and 'Replace this paragraph and the checklist below with measured final results before posting.' in new_pr.decode(), 'planned PR remains explicitly draft pending final measured results')
difference(old_pr, new_pr, 'PR-BODY.md')

old_note = read(P / 'overlay' / note_path)
new_note = read(W / note_path)
old_identifier = r'\texttt{NLA.RA02.universal\_counterexamples}'
new_identifier = r'\nolinkurl{NLA.RA02.universal_counterexamples}'
check(old_note.decode().count(old_identifier) == 1 and new_note.decode() == old_note.decode().replace(old_identifier, new_identifier, 1), 'sole note change permits line breaks in the same theorem identifier')
check(sha(new_note) == record['note_source_sha256'], 'exact corrected note source digest')
difference(old_note, new_note, 'solution.tex')
layout = W / REL / 'verification/publication/layout'
check(read(layout / 'before-solution.tex.txt') == old_note, 'exact original note snapshot')
expected_patch = ''.join(difflib.unified_diff(old_note.decode().splitlines(True), new_note.decode().splitlines(True), fromfile='before/solution.tex', tofile='after/solution.tex')).encode()
check(read(layout / 'REPAIR.patch') == expected_patch and sha(expected_patch) == record['note_layout_patch_sha256'], 'root layout patch is exactly the one-line semantic-preserving change')
check(read(QA / 'solution.tex') == new_note and read(QA / 'layout-repair/REPAIR.patch') == expected_patch, 'private final render input and recorded patch match applied source')
check(read(QA / 'layout-repair/solution.tex') == old_note, 'layout-repair subdirectory is the exact before-repair source backup')
before_build = js(QA / 'layout-repair/BUILD.json')
check(before_build['source_sha256'] == sha(old_note) and before_build['warnings'] == ['Overfull \\hbox (8.4785pt too wide) in paragraph at lines 43--50'], 'before-repair root record identifies the precise overflow repaired')
build = js(layout / 'BUILD.json')
check(build == record['actual_note_render'] == js(QA / 'BUILD.json'), 'exact root build record copies')
check(build['source_sha256'] == sha(new_note) and build['warnings'] == [], 'root build record source and warning status')
expected_argv = ['/Library/TeX/texbin/pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'solution.tex']
check(len(build['runs']) == 2 and all(row['argv'] == expected_argv and row['exit_code'] == 0 and row['pass'] == i + 1 for i, row in enumerate(build['runs'])), 'root records two successful exact TeX passes')
pdf = read(W / BASE / 'solution.pdf')
check(pdf == read(QA / 'solution.pdf') and sha(pdf) == record['note_PDF_sha256'] and pdf.startswith(b'%PDF-'), 'applied note PDF equals recorded root render artifact')
for n in [1, 2]:
    log = read(layout / f'solution-pass{n}.log.txt')
    check(log == read(QA / f'solution-pass{n}.log.txt'), 'retained root render log equals private original pass ' + str(n))
    check(f'Output written on solution.pdf (2 pages, {len(pdf)} bytes).'.encode() in log, 'root log reports two-page PDF with exact artifact byte length pass ' + str(n))
    check(not re.search(rb'Overfull|Underfull|LaTeX Warning|Package .* Warning|^!', log, re.M), 'root retained render log has no matched errors, warnings or box overflow pass ' + str(n))
for filename, digest in record['note_visual_review']['image_sha256'].items():
    check(sha(read(QA / filename)) == digest, 'root visual-review image digest, hash check only ' + filename)
check(record['note_visual_review']['reviewer'] == '/root', 'visual-inspection authorship remains root, not this referee')

old_index = read(P / 'overlay' / index_path)
new_index = read(W / index_path)
expected_index = json.loads(old_index)
expected_index['publication_overlay_reviews'] = [{'path': 'reviews/publication-overlay/REVIEW.md', 'manifest_sha256': sha(read(PRIOR / 'MANIFEST.json')), 'scope': 'Independent conditional document review; one PR attribution correction applied by coordinator, bounded follow-through pending'}]
check(new_index == (json.dumps(expected_index, indent=2) + '\n').encode() and sha(new_index) == record['current_index_sha256'], 'INDEX only adds the exact scoped prior-review link')
difference(old_index, new_index, 'lean/reviews/INDEX.json')
check('Pending coordinator assignment and independent review' in expected_index['publication_review'], 'remaining current publication-state transition explicitly identified, not silently treated as historical')

additional = {}
for path in PRIOR.iterdir():
    if path.is_file():
        target = W / REL / 'reviews/publication-overlay' / path.name
        check(read(target) == read(path), 'unchanged attached conditional publication review ' + path.name)
        additional[target.relative_to(W).as_posix()] = sha(read(target))
for path in layout.iterdir():
    if path.is_file():
        additional[path.relative_to(W).as_posix()] = sha(read(path))
check({x.name for x in layout.iterdir() if x.is_file()} == {'before-solution.tex.txt', 'REPAIR.patch', 'BUILD.json', 'solution-pass1.log.txt', 'solution-pass2.log.txt'}, 'exact five attached note-layout evidence files')
root_applied = W / REL / 'verification/publication/ROOT-APPLIED.json'
check(read(root_applied) == record_data, 'ROOT-APPLIED byte-identical root transition record')
additional[root_applied.relative_to(W).as_posix()] = sha(read(root_applied))
additional[BASE + '/solution.pdf'] = sha(pdf)
check(len(additional) == 31, '24 prior-review files, five layout files, root transition and note PDF enumerated separately')
check(read(W / REL / 'formalization.yaml') == read(P / 'overlay' / REL / 'formalization.yaml'), 'applied formalization metadata remains byte-identical to the previously validated 27-declaration proposal')
prior_validation = js(PRIOR / 'MANIFEST-VALIDATION.json')
check(prior_validation['exit_code'] == 0 and sha(read(PRIOR / 'MANIFEST-VALIDATION.log')) == prior_validation['log_sha256'], 'prior actual metadata-validator receipt preserved; no redundant new validator invocation')

summary = {'reviewer': '/root/sf_ra_runtime_referee', 'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'verdict': 'APPROVED: exact RA02 requested attribution correction, note source layout correction, and enumerated evidence additions. No requested correction remains within this bounded scope.', 'scope': 'Independent source/evidence correction follow-through; not PDF rendering or visual inspection, proof execution, catalog/ID or final publication acceptance.', 'root_correction_record_sha256': sha(record_data), 'original_proposal_manifest_sha256': record['overlay_manifest_sha256'], 'prior_conditional_review_manifest_sha256': record['conditional_review_manifest_sha256'], 'passed_assertions': len(checks), 'external_bindings': len(bindings), 'original_overlay_paths': 44, 'protected_original_inputs': 220, 'unchanged_non_document_original_inputs': 216, 'unchanged_mathematical_sources': 35, 'prior_bindings': len(old_bindings), 'unchanged_prior_bindings': len(old_bindings) - len(transitioned), 'old_document_bindings_preserved_by_before_snapshots': transitioned, 'corrected_PR_sha256': sha(new_pr), 'corrected_note_source_sha256': sha(new_note), 'note_PDF_sha256': sha(pdf), 'current_INDEX_sha256': sha(new_index), 'additional_evidence_files': additional, 'root_PDF_evidence_scope': 'Full two-pass logs and exact source, patch, PDF and two image digests checked; root is the reported render and visual reviewer. This referee neither rendered nor viewed a PDF/image.', 'metadata_validator_scope': 'Prior actual PASS for 27 declarations is preserved; applied YAML is byte-identical. No fresh validation is claimed in this follow-through.', 'remaining_separate_gates': ['Root must advance the current publication metadata, including the still-pending INDEX publication_review field, to measured review/PDF/catalog status with separate source-bound transition evidence', 'Canonical PDF render and visual inspection, catalog/permanent-ID checks and their records', 'Replace planned PR draft checklist with measured results before posting', 'Actual exact publication and upstream PR checkout checks'], 'no_Git_compiler_Lean_Lake_Comparator_PDF_catalog_ID_worktree_raw_publication_count_mutation': True}
summary['applied_overlay_scope'] = '40 applied paths equal the sealed proposal; note TeX and review INDEX have the exact bounded changes reviewed here; concurrent canonical README date correction and problem.tex regeneration are explicitly excluded and separately observed.'
summary['concurrent_canonical_gate_excluded'] = excluded_canonical
summary['remaining_separate_gates'].insert(1, 'Preserve the actual historical literature-check date in the separately regenerated canonical TeX/PDF; no new literature search is implied by proof verification')
for filename, data in [('CHECKS.json', summary), ('ASSERTIONS.json', checks), ('SOURCE-BINDINGS.json', bindings)]:
    (OUT / filename).write_text(json.dumps(data, indent=2, sort_keys=filename == 'SOURCE-BINDINGS.json') + '\n')
(OUT / 'CORRECTIONS.diff').write_text(''.join(diffs))
print(json.dumps({'passed': True, 'assertions': len(checks), 'external_bindings': len(bindings), 'overlay_paths': 44, 'unchanged_mathematical_sources': 35, 'unchanged_non_document_inputs': 216, 'enumerated_additional_files': len(additional), 'required_corrections_remaining': 0}))

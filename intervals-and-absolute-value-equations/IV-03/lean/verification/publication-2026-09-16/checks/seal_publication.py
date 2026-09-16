"""Seal document preparation after actual validators and visual inspection.

This executes no Lean/Lake, changes no Git refs/index/config, and publishes nothing.
It is a preparer's reconciliation, not a new independent mathematical review.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile
import yaml

W = Path('/private/tmp/nla-lean-next-iv03-worktree')
B = Path('/tmp/nla-lean-next-20260915')
S = W / '.iv03-publication-preparation'
ID = 'intervals-and-absolute-value-equations/IV-03'
P = W / ID / 'lean'
PUB = P / 'verification/publication-2026-09-16'
C = 'cef3e2f486285d0f6885231cda3ac2ff04c975cb'
R = B / 'canonical-runs/IV03-35059255598'
I = B / 'reviews/IV03-import-independent'
EMAIL = re.compile(rb'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def digest(path):
    return sha(path.read_bytes())

def git(*args):
    return subprocess.check_output(['git', '-C', str(W), *args])

def put(path, value):
    data = value.encode() if isinstance(value, str) else value
    assert not EMAIL.search(data), f'Email in new public bytes: {path}'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)

def dump(path, value):
    put(path, json.dumps(value, indent=2, ensure_ascii=False) + '\n')

assert not (P / 'PUBLICATION-MANIFEST.json').exists(), 'A prior seal already exists; do not overwrite it.'
assert not (S / 'SEALED-PUBLICATION.json').exists()
assert git('rev-parse', 'HEAD').decode().strip() == C
expected_changed = {
    'CATALOG.md', 'README.md', 'RESOLVED.md', 'intervals-and-absolute-value-equations/README.md',
    'tools/render_problems.py', ID + '/README.md', ID + '/problem.tex', ID + '/problem.pdf',
    ID + '/lean/README.md', ID + '/lean/formalization.yaml'}
changed = set(git('diff', '--name-only').decode().splitlines())
assert changed == expected_changed, changed ^ expected_changed
diff = subprocess.run(['git', 'diff', '--check'], cwd=W, text=True, capture_output=True)
assert diff.returncode == 0, diff.stdout + diff.stderr

receipt_path, = (R / 'artifacts/lean-IV-03').glob('verify-*/result.json')
receipt = json.loads(receipt_path.read_text())
transition = json.loads((PUB / 'TRANSITION.json').read_text())
protected = transition['protected_inputs']
assert len(protected) == 138 and len(receipt['input_sha256']) == 140
assert transition['all140_accepted_inputs'] == receipt['input_sha256']
original_bindings = {}
for name, original in receipt['input_sha256'].items():
    assert sha(git('show', C + ':' + ID + '/lean/' + name)) == original
    current = digest(P / name)
    if name in protected:
        assert current == original, name
    else:
        assert name in {'README.md', 'formalization.yaml'} and current != original
        assert digest(PUB / 'before/lean' / name) == original
    original_bindings[name] = {'accepted_sha256': original, 'publication_sha256': current, 'unchanged': current == original}

active = json.loads((R / 'mi04-independent/ALL-14-ACTIVE-SOURCE-BINDINGS.json').read_text())
assert len(active) == 14
for name, row in active.items():
    assert digest(P / name) == row['sha256']
frozen = json.loads((P / 'statement-freeze.json').read_text())
assert len(frozen['sha256']) == 7
for name, value in (frozen['sha256'] | frozen['reports']).items():
    assert digest(P / name) == value
current_lean = {str(x.relative_to(P)): digest(x) for x in P.rglob('*.lean')}
old_lean = {n: h for n, h in receipt['input_sha256'].items() if n.endswith('.lean')}
assert current_lean == old_lean and len(current_lean) == 21

before_docs = {}
for name in sorted(expected_changed - {ID + '/lean/README.md', ID + '/lean/formalization.yaml'}):
    original = git('show', C + ':' + name)
    assert (PUB / 'before' / name).read_bytes() == original
    before_docs[name] = {'before_sha256': sha(original), 'after_sha256': digest(W / name)}
old_readme = (PUB / 'before' / ID / 'README.md').read_text()
new_readme = (W / ID / 'README.md').read_text()
assert old_readme.split('## Problem statement\n', 1)[1] == new_readme.split('## Problem statement\n', 1)[1]
old_archive = (PUB / 'before/RESOLVED.md').read_text()
new_archive = (W / 'RESOLVED.md').read_text()
old_start = old_archive.index('### IV-03 - Affirmative resolution')
new_start = new_archive.index('### 🏆 IV-03 - Affirmative resolution with Lean verification')
assert old_archive[:old_start] == new_archive[:new_start]
old_end = old_archive.index('\n### ', old_start + 1)
new_end = new_archive.index('\n### ', new_start + 1)
assert old_archive[old_end:] == new_archive[new_end:]
manuscripts = {}
for extension in ('tex', 'pdf'):
    name = 'references/colbrook-intervals-2026-09-11/manuscripts/IV-03.' + extension
    value = digest(W / name)
    assert value == sha(git('show', C + ':' + name))
    manuscripts[name] = value
for name in ['tools/lean', '.github/workflows/lean-verification.yml', 'docs/lean', 'problem_ids.json', 'references']:
    assert not git('diff', C, '--', name), name
materialized = json.loads((PUB / 'SPARSE-METADATA-MATERIALIZATION.json').read_text())
for row in materialized['files']:
    name = row['path']
    assert row['sha256'] == sha(git('show', C + ':' + name))
    if name != 'intervals-and-absolute-value-equations/README.md':
        assert digest(W / name) == row['sha256'], name

# Read every retained actual evidence file, not just a success field, back against
# the already authenticated original; this is transport reconciliation only.
runtime_map = {}
for source in sorted(R.rglob('*')):
    if source.is_file():
        name = str(source.relative_to(R))
        assert digest(P / 'verification/linux-2026-09-16' / name) == digest(source)
        runtime_map[name] = digest(source)
import_map = {}
for source in sorted(I.rglob('*')):
    if source.is_file():
        name = str(source.relative_to(I))
        assert digest(P / 'reviews/campaign/import-review' / name) == digest(source)
        import_map[name] = digest(source)
assert digest(R / 'lean-IV-03.zip') == '65608be436508a0350c4d22e0e18f15e5e6706fc131f2e841707747f01e9a5e7'
assert digest(receipt_path) == '517132922f1bc222b9466545c9011c48a42d2bbfeff427e577de8d51d11f239b'

meta = yaml.safe_load((P / 'formalization.yaml').read_text())
comparator = json.loads((P / 'comparator.json').read_text())
assert meta['project']['authors'] == ['Sidney Holden']
assert meta['project']['license'] == 'Apache-2.0'
assert meta['submission']['role'] == 'integration and verification submission'
assert set(x['declaration'] for x in meta['status']['main_results']) == set(comparator['theorem_names'])
assert len(comparator['theorem_names']) == 4 and comparator['definition_names'] == []
assert set(meta['status']['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
for doc in [new_readme, new_archive[new_start:new_end], (P / 'README.md').read_text()]:
    for name in ['Matthew J. Colbrook', 'Sidney Holden', 'George Stepaniants', 'Department of Computing and Mathematical Sciences', 'California Institute of Technology']:
        assert name in ' '.join(doc.split())
assert all(meta['verification'][key] == value for key, value in {'proof_commit': C, 'canonical_inputs': 140, 'frozen_exports': 4}.items())

validator_results = {}
for name in ['schema', 'permanent-ids', 'catalog', 'id-tests', 'render-final']:
    result = json.loads((S / (name + '.json')).read_text())
    assert result['exit_code'] == 0
    validator_results[name] = result
assert 'PASS (4 declarations)' in (S / 'schema.log').read_text()
assert 'Validated 217 permanent problem IDs against origin/main' in (S / 'permanent-ids.log').read_text()
assert 'Ran 17 tests' in (S / 'id-tests.log').read_text()
assert (S / 'render-final.log').read_text() == 'IV-03: OK\nRendered 1 problem documents.\n'
assert 'Overfull' in (S / 'render.log').read_text()

docs = [W / ID / 'README.md', P / 'README.md', P / 'reviews/final/README.md',
        P / 'verification/linux-2026-09-16/README.md', PUB / 'README.md',
        PUB / 'public-duplicate-audit/README.md']
links = []
for source in docs:
    for target in re.findall(r'(?<!!)\[[^\]]*\]\(([^)]+)\)', source.read_text()):
        if re.match(r'[a-z]+:', target) or target.startswith('#'):
            continue
        path = (source.parent / target.split('#', 1)[0]).resolve()
        assert path.is_relative_to(W)
        assert path.exists(), (source, target)
        links.append({'source': str(source.relative_to(W)), 'target': target, 'resolved': str(path.relative_to(W)), 'exists': True})

pdf = W / ID / 'problem.pdf'
pdf_record = json.loads((S / 'pdf-review-final/RENDER.json').read_text())
assert pdf_record['pdf_sha256'] == digest(pdf)
assert len(pdf_record['pages']) == 4
for name, value in pdf_record['pages'].items():
    assert digest(S / 'pdf-review-final' / name) == value
pdf_text = (S / 'pdf-review-final/problem.txt').read_text()
assert not EMAIL.search(pdf_text.encode())
for token in ['35059255598', '104675949451', C, 'Lean verified', 'Matthew J. Colbrook', 'Sidney Holden', 'George Stepaniants', 'California Institute of Technology']:
    assert token in pdf_text, token

# All final pages were viewed with view_image in this actual task after the
# second two-pass XeLaTeX render; this is the human-facing agent visual record.
pdf_review = {
    'reviewer': '/root/mi04_independent_referee',
    'pdf_sha256': digest(pdf), 'tex_sha256': digest(W / ID / 'problem.tex'),
    'pages': pdf_record['pages'], 'all4_pages_visually_inspected': True,
    'page1': 'Title, retained informal resolution and Colbrook authorship are legible; no clipping or overlapping elements.',
    'page2': 'All three roles/affiliations, all four exports and exact run/commit are visible; the corrected commit paragraph fits within the margin.',
    'page3': 'The entire unchanged original interval and two-sign equivalence appears together, with no clipped formulas or lost quantifiers.',
    'page4': 'Original references and dated historical audits are complete and legible.',
    'initial_observed_issue': 'One overfull horizontal box in the new runtime paragraph, 16.52925pt; initial render and logs are retained.',
    'correction': 'Moved the full literal checked commit to its own paragraph in canonical Markdown; no mathematical statement or proof source changed.',
    'final_renderer': 'Two XeLaTeX passes, zero overfull/missing-character warnings.',
    'contact_email_matches_in_extracted_PDF': 0,
    'marker': 'PDF-SKILL-MARKER.json; executed exactly once, not repeated for the corrected render.'}

privacy = []
paths = list(x for x in P.rglob('*') if x.is_file()) + [W / n for n in sorted(expected_changed) if not n.startswith(ID + '/lean/')]
for path in paths:
    assert not EMAIL.search(path.read_bytes()), path
    item = {'path': str(path.relative_to(W)), 'sha256': digest(path), 'email_matches': 0}
    if path.suffix == '.zip':
        with zipfile.ZipFile(path) as z:
            assert all(not EMAIL.search(z.read(n)) for n in z.namelist()), path
            item['zip_members_screened'] = len(z.namelist())
    privacy.append(item)

# Only after every preflight assertion passes, emit the public audit and seal.
for name in ['schema', 'permanent-ids', 'catalog', 'id-tests', 'render', 'render-final']:
    for extension in ['json', 'log']:
        put(PUB / 'checks' / (name + '.' + extension), (S / (name + '.' + extension)).read_bytes())
put(PUB / 'checks/diff-check.log', diff.stdout + diff.stderr)
put(PUB / 'checks/prepare_publication.py', (S / 'prepare_publication.py').read_bytes())
put(PUB / 'checks/seal_publication.py', Path(__file__).read_bytes())
dump(PUB / 'checks/ALL-140-TRANSITIONS.json', original_bindings)
dump(PUB / 'checks/CANONICAL-DOCUMENT-TRANSITIONS.json', before_docs)
dump(PUB / 'checks/EXACT-RUNTIME-TRANSPORT.json', runtime_map)
dump(PUB / 'checks/EXACT-IMPORT-REVIEW-TRANSPORT.json', import_map)
dump(PUB / 'checks/LINK-CHECKS.json', {'documents': len(docs), 'links': links})
dump(PUB / 'checks/PDF-REVIEW.json', pdf_review)
dump(PUB / 'checks/PRIVACY-CHECKS.json', {
    'scope': 'All prepared project inputs and changed canonical documents screened; every ZIP member additionally screened and final PDF text checked. Contact-bearing original manuscript not duplicated.',
    'files': privacy, 'email_matches': 0})
checks = {
    'reviewer': '/root/mi04_independent_referee', 'role': 'publication preparer and transport auditor, not an independent reviewer of its own documentation',
    'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'proof_commit': C,
    'source_acceptance': 'Real canonical run35059255598/job104675949451; independently audited before this preparation.',
    'protected_original_inputs': 138, 'accepted_original_inputs': 140,
    'changed_original_metadata': ['README.md', 'formalization.yaml'],
    'all14_active_sources_unchanged': True, 'all21_original_Lean_files_unchanged': True,
    'all7_frozen_inputs_and2_statement_reviews_unchanged': True,
    'original_target_from_problem_statement_heading_unchanged': True,
    'original_manuscript_tex_and_pdf_unchanged': manuscripts,
    'all_prior_review_import_and_evidence_bytes_unchanged': True,
    'only_IV03_resolution_entry_changed': True,
    'shared_checker_workflow_pins_and_ID_registry_unchanged': True,
    'all_missing_sparse_metadata_materialized_from_existing_exact_Git': len(materialized['files']),
    'exact_runtime_files_retained': len(runtime_map), 'exact_import_audit_files_retained': len(import_map),
    'source_and_formalization_authorship_and_license_preserved': True,
    'Stepaniants_role_affiliation_and_department_correct': True,
    'validator_commands': validator_results, 'ID_tests_passed': 17, 'canonical_IDs_validated': 217,
    'final_PDF_pages_visually_checked': 4, 'final_PDF_layout_warnings': 0,
    'public_email_matches': 0, 'current_authored_links_resolve': len(links),
    'Git_diff_check_exit_code': diff.returncode,
    'local_Lean_Lake_or_cache': False, 'Git_commit_push_PR_or_campaign_count': False,
    'root_publication_review': 'pending separate reviewer',
    'later_publication_commit_and_upstream_merge_runs': 'pending; no unexecuted success claim'}
dump(PUB / 'CHECKS.json', checks)
put(PUB / 'PREPARER-REPORT.md', '''# IV-03 publication preparation for independent root review

**Prepared and checked, not committed or published.** This is the publication
preparer's record, not independent approval of its own documentation. The actual
fresh Linux acceptance at `cef3e2f486285d0f6885231cda3ac2ff04c975cb`, run
35059255598/job104675949451, had already been independently authenticated before
this step. Root will separately review these documents and the publication
transition. Later publication and upstream commits require their own real runs.

Only the accepted project's README and formalization.yaml change. Every other
accepted input is byte-identical: 138 protected inputs, including all fourteen
active Lean files, all seven frozen inputs, the two statement-review hashes,
dependency/checker configuration, license, original reviews, historical evidence
and original package/source inventories. The complete canonical mathematical
target is unchanged from its heading onward. Colbrook's original manuscript TeX
and PDF are unchanged, and no contact-bearing copy is added. The retained-before
files and exact before/after maps document all changes.

The canonical README, RESOLVED entry, generated catalog indexes and PDF describe
the complete n-squared and original two-sign equivalences. Colbrook retains
mathematical credit with Cambridge DAMTP; Sidney Holden retains formalization
credit and Apache-2.0; George Stepaniants is credited for integration/verification,
Department of Computing and Mathematical Sciences, California Institute of
Technology. Existing source attribution and AI-assistance disclosures remain.

All actual fresh-run evidence and the independent import review were transported
byte-for-byte and reconciled. Raw API/log records and every archive member passed
contact-email screening. The helper's fixed /root reviewer label is disclosed as
the actual inequalities-referee invocation. No independent second execution by
each reviewer, external human review, official Tau Ceti endorsement or infallible
checker/platform is claimed. Earlier pending-stage inventories and reports remain
untouched and are explicitly identified as historical records.

The real schema validator passed all four declarations. The permanent-ID
validator passed all 217 IDs against the recorded origin/main; catalog generation
completed and all 17 permanent-ID tests passed. Only the IV-03 row/status changes
in generated indexes. Missing sparse metadata were materialized exclusively from
the existing tested Git commit; no Git configuration, registry or safeguards changed.

The canonical TeX/PDF was generated through the repository renderer with two
XeLaTeX passes. After one observed long-hash overflow was fixed by a paragraph
break, the final renderer reported no overfull or missing-character warnings.
I viewed every final rendered page: original resolution/authorship, new evidence,
complete retained statement, and historical references/audits. All are legible,
complete and unclipped. The renderer changes are restricted to IV-03 page breaks
and its verification-date footer label. Exact PDF/PNG hashes and page findings
are in checks/PDF-REVIEW.json; scratch images are not publication inputs.

No Lean, Lake or cache computation ran locally. No proof implementation, Git
index/ref/config, commit, push, PR or campaign count was changed. The untracked
.iv03-publication-preparation directory is local working evidence and must not
be added wholesale to a publication commit. PUBLICATION-MANIFEST.json inventories
the prepared project; the separate SEALED-PUBLICATION.json also binds the changed
canonical repository documents and exact tested proof baseline.
''')

# One manifest inventories every prepared project file except itself; the
# external seal below includes it, avoiding self-referential hash cycles.
project_files = {str(p.relative_to(P)): digest(p) for p in sorted(P.rglob('*')) if p.is_file()}
dump(P / 'PUBLICATION-MANIFEST.json', {
    'scope': 'Prepared complete IV-03 publication project, excluding only this manifest itself. Original MANIFEST.json remains the unchanged historical import inventory.',
    'proof_commit': C, 'actual_proof_run': 35059255598,
    'root_publication_review_and_later_commit_execution': 'pending',
    'files': project_files})
project_files['PUBLICATION-MANIFEST.json'] = digest(P / 'PUBLICATION-MANIFEST.json')
repository_documents = {n: digest(W / n) for n in sorted(expected_changed) if not n.startswith(ID + '/lean/')}
seal = {
    'scope': 'Review-ready uncommitted IV-03 publication package; project files plus eight changed repository documents.',
    'prepared_by': '/root/mi04_independent_referee', 'worktree': str(W),
    'unchanged_HEAD': C, 'project_path': ID + '/lean',
    'project_input_count_including_publication_manifest': len(project_files),
    'project_inputs': project_files, 'changed_repository_documents': repository_documents,
    'publication_checks_sha256': digest(PUB / 'CHECKS.json'),
    'preparer_report_sha256': digest(PUB / 'PREPARER-REPORT.md'),
    'publication_manifest_sha256': digest(P / 'PUBLICATION-MANIFEST.json'),
    'PDF_sha256': digest(pdf), 'PDF_pages_checked': 4,
    'original_tested_input_count': 140, 'original_tested_run': 35059255598,
    'no_commit_push_PR_count_or_local_Lean': True,
    'not_for_commit': '.iv03-publication-preparation scratch directory; selected scripts/check records are already copied into the publication project.'}
dump(S / 'SEALED-PUBLICATION.json', seal)
print(json.dumps({
    'seal': str(S / 'SEALED-PUBLICATION.json'), 'seal_sha256': digest(S / 'SEALED-PUBLICATION.json'),
    'project_inputs': len(project_files), 'changed_repository_documents': len(repository_documents),
    'publication_manifest_sha256': digest(P / 'PUBLICATION-MANIFEST.json'),
    'checks_sha256': digest(PUB / 'CHECKS.json'), 'PDF_sha256': digest(pdf),
    'verdict': 'Prepared and sealed for independent root publication review; no publishing performed.'}, indent=2))

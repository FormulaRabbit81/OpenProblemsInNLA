"""Seal KE-05 publication preparation checks; no local Lean or Git mutation."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile
import yaml
import jsonschema

B = Path('/tmp/nla-lean-next-20260915')
W = Path('/private/tmp/nla-lean-next-ke05-worktree')
ID = 'randomized-and-low-rank-approximation/KE-05'
P = W / ID / 'lean'
PUB = P / 'verification/publication-2026-09-16'
OUT = PUB / 'checks'
OUT.mkdir(exist_ok=True)
C = '414371c9a76aafd7477d9705f9644f7efeb5e329'
IMAGES = B / 'tmp/pdfs/ke05-publication'

def sha(b): return hashlib.sha256(b).hexdigest()
def digest(p): return sha(p.read_bytes())
def load(p): return json.loads(p.read_text())
def dump(p, value): p.write_text(json.dumps(value, indent=2) + '\n')
def git(*args): return subprocess.check_output(['git', '-C', str(W), *args])

assert git('rev-parse', 'HEAD').decode().strip() == C
t = load(PUB / 'TRANSITION.json')
assert len(t['all151_accepted_inputs']) == 151 and len(t['protected_inputs']) == 149
for name, value in t['protected_inputs'].items(): assert digest(P / name) == value
for name in t['metadata_updated']:
    assert digest(PUB / 'before/lean' / name) == t['all151_accepted_inputs'][name]
for name, value in t['retained_original_manuscripts'].items(): assert digest(W / name) == value
page = (P.parent / 'README.md').read_text()
old = (PUB / 'before' / ID / 'README.md').read_text()
assert page.split('## Original statement (retained)\n', 1)[1] == old.split('## Original statement (retained)\n', 1)[1]
assert '**Status:** Lean verified\n' in page and '**Last checked:** 2026-09-16\n' in page
assert 'Formalization: Sidney Holden' in page and 'George Stepaniants' in page and 'Nian Shao' in page
assert C in page and '35058392398' in page and '104673346252' in page
for prefix in ['tools/lean', '.github/workflows/lean-verification.yml', 'docs/lean', 'problem_ids.json']:
    assert git('diff', C, '--', prefix) == b''
ids = load(W / 'problem_ids.json')
for name in ids.values():
    if name != ID + '/README.md': assert (W / name).read_bytes() == git('show', C + ':' + name)
assert len(ids) == 217
config = load(P / 'comparator.json')
metadata = yaml.safe_load((P / 'formalization.yaml').read_text())
jsonschema.validate(metadata, load(W / 'docs/lean/schema/v0.4.schema.json'))
assert metadata['project']['authors'] == ['Sidney Holden']
assert metadata['project']['responsible_maintainers'] == ['George Stepaniants']
assert metadata['status']['whole_problem_verified']
assert [r['declaration'] for r in metadata['status']['main_results']] == config['theorem_names']
assert len(config['theorem_names']) == 10
assert metadata['verification']['proof_commit'] == C

# Exact preservation of every copied canonical evidence and runtime-review byte.
R = B / 'canonical-runs/KE05-35058392398'
copied = []
for f in sorted(R.rglob('*')):
    if not f.is_file(): continue
    dst = P / 'verification/linux-2026-09-16' / f.relative_to(R)
    assert f.read_bytes() == dst.read_bytes()
    copied.append({'path': str(dst.relative_to(P)), 'sha256': digest(f)})
A = B / 'reviews/KE05-mf22-independent/canonical35058392398-addendum'
for f in sorted(A.rglob('*')):
    if not f.is_file(): continue
    dst = P / 'reviews/campaign/canonical-run-35058392398' / f.relative_to(A)
    assert f.read_bytes() == dst.read_bytes()
    copied.append({'path': str(dst.relative_to(P)), 'sha256': digest(f)})
dump(OUT / 'COPIED-EVIDENCE-AND-REFEREE-BINDINGS.json', copied)
dup = load(PUB / 'public-duplicate-audit/RETAINED-FILES.json')
for name, value in dup['bounded_retained_files'].items(): assert digest(PUB / 'public-duplicate-audit' / name) == value
marker = load(PUB / 'PDF-SKILL-MARKER.json')
assert marker['exit_code'] == 0 and marker['tool_chunk_id'] == 'ac50c8'

read_paths = [P.parent / 'README.md', P / 'README.md', P / 'reviews/final/README.md',
              P / 'verification/linux-2026-09-16/README.md']
links = []
for path in read_paths:
    for target in re.findall(r'\]\(([^)]+)\)', path.read_text()):
        if re.match(r'[a-zA-Z]+:', target) or target.startswith('#'): continue
        pure = target.split('#', 1)[0]
        dest = (path.parent / pure).resolve()
        relative = str(dest.relative_to(W))
        if dest.exists(): status = 'exists in current prepared worktree'
        else:
            assert path == P.parent / 'README.md' and '](' + target + ')' in old
            git('cat-file', '-e', C + ':' + relative)
            status = 'historical link exists in exact Git tree; omitted only by sparse worktree'
        links.append({'from': str(path.relative_to(W)), 'to': target, 'status': status})
dump(OUT / 'PUBLICATION-LINKS.json', links)

changed = git('diff', '--name-only').decode().splitlines()
expected = {'CATALOG.md', 'README.md', 'RESOLVED.md', 'randomized-and-low-rank-approximation/README.md',
    ID + '/README.md', ID + '/problem.tex', ID + '/problem.pdf', ID + '/lean/README.md',
    ID + '/lean/formalization.yaml', 'tools/render_problems.py'}
assert set(changed) == expected, changed
new = git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(s.startswith(ID + '/lean/') for s in new)
assert not any(s.endswith('.lean') for s in changed + new)
email = re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
for rel in changed + new:
    path = W / rel
    if path.suffix == '.zip':
        with zipfile.ZipFile(path) as z:
            for name in z.namelist():
                if not name.endswith('/'):
                    assert not email.search(z.read(name).decode(errors='replace')), (rel, name)
    elif path.suffix not in {'.pdf', '.png'}:
        assert not email.search(path.read_text(errors='replace')), rel
pdf = P.parent / 'problem.pdf'
pdf_info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
assert re.search(r'^Pages:\s+4$', pdf_info, re.M)
pdf_text = subprocess.check_output(['pdftotext', str(pdf), '-'], text=True)
assert not email.search(pdf_text)
assert all(s in pdf_text for s in ['Sidney Holden', 'George Stepaniants', 'Mathematical Sciences', 'California Institute of Technology', 'Nian Shao', '35058392398', '104673346252'])
(OUT / 'pdfinfo.txt').write_text(pdf_info)
images = {f'page-{i}.png': digest(IMAGES / f'page-{i}.png') for i in range(1, 5)}
diff = subprocess.run(['git', 'diff', '--check'], cwd=W, capture_output=True, text=True)
assert diff.returncode == 0, diff.stdout + diff.stderr
dump(OUT / 'ACTUAL-PREPARATION-COMMANDS.json', {
    'scope': 'Observed tool executions during this publication preparation; these are not new Lean executions.',
    'commands': [
        {'command': 'python tools/lean/validate_manifest.py randomized-and-low-rank-approximation/KE-05/lean', 'tool_chunk': '8158a1', 'exit_code': 0, 'result': 'Manifest schema and comparator coverage: PASS (10 declarations)'},
        {'command': 'python3 tools/validate_problem_ids.py --base-ref origin/main', 'tool_chunk': '38844e', 'exit_code': 0, 'result': 'Validated 217 permanent problem IDs against origin/main'},
        {'command': 'python3 tools/update_catalog.py --base-ref origin/main', 'tool_chunk': '2dee43', 'exit_code': 0, 'result': 'Indexed 217 entries; branch-local generated counts, not a campaign completion count'},
        {'command': 'python3 -m unittest discover -s tests -p test_problem_ids.py -v', 'tool_chunk': 'd1367a', 'exit_code': 0, 'result': 'All 17 permanent-ID tests passed'},
        {'command': 'python3 tools/format_math.py --check KE-05', 'tool_chunk': '3fd4c1', 'exit_code': 0, 'result': 'Need formatting: 0 pages'},
        {'command': 'PANDOC=/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc python3 tools/render_problems.py KE-05', 'tool_chunk': '7b8c1b', 'exit_code': 0, 'result': 'KE-05: OK; Rendered 1 problem documents.'},
        {'command': 'git diff --check', 'execution': 'executed within this sealing script after whitespace repair', 'exit_code': diff.returncode, 'stdout': diff.stdout, 'stderr': diff.stderr}],
    'resolved_initial_issues': ['First PDF render had an overfull theorem-name line; two explicit theorem bullets removed it before the successful final render.', 'Initial diff check found two inherited metadata trailing-space lines; they were removed and renderer values/body proved identical. The inspected PDF remains current.']})
checks = {
    'prepared_and_checked_by': '/root/mf22_publication_referee',
    'kind': 'publication-preparation self-check; separate root publication review required',
    'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'proof_commit': C,
    'canonical_run': 35058392398, 'canonical_job': 104673346252,
    'all149_prior_nonmetadata_inputs_unchanged': True,
    'all23_mathematical_Lean_files_unchanged': True,
    'all_frozen_statement_and_configuration_bytes_preserved': True,
    'current_accepted_Lake_default_Solution_unchanged': True,
    'only_original_project_metadata_changes': ['README.md', 'formalization.yaml'],
    'original_metadata_beforebytes_retained': True,
    'full_original_canonical_target_from_retained_heading_unchanged': True,
    'all_original_solution_files_unchanged': t['retained_original_manuscripts'],
    'all_other216_canonical_READMEs_equal_accepted_Git_blobs': True,
    'all_copied_source_reviews_import_history_and_actual_evidence_preserved': True,
    'copied_fresh_evidence_and_runtime_review_records': len(copied),
    'source_reviewers_and_actual_executor_roles_disclosed': True,
    'formalization_author': 'Sidney Holden',
    'mathematical_and_integration_author': 'George Stepaniants, Caltech Department of Computing and Mathematical Sciences',
    'original_framework_author': 'Nian Shao',
    'public_duplicate_scope': '14 public repositories, 249 heads, 203 unique trees; explicit reuse of existing Sidney Holden formalization, no priority or public-absence claim',
    'local_links_checked': len(links), 'all_links_resolve_in_worktree_or_exact_Git': True,
    'no_contact_email_in_changed_new_text_zip_payloads_or_PDF_text': True,
    'schema_v04_valid': True, 'exact_export_manifest_coverage': 10,
    'permanent_ID_validator': '217 IDs pass against origin/main', 'required_permanent_ID_tests': '17 passed',
    'catalog_regenerated': True, 'format_math': '0 pages need changes', 'diff_check': 'pass',
    'tracked_changes': {p: digest(W / p) for p in changed},
    'PDF': {'path': ID + '/problem.pdf', 'sha256': digest(pdf), 'pages': 4,
        'render': 'latest renderer reported KE-05: OK with no layout/missing-character warning',
        'visual_inspection': 'All four final 110dpi PNG pages inspected; title, author/affiliation, formal theorem names, equations, evidence, complete original target and historical references are legible, with no clipping, overlap or missing glyphs.',
        'page_image_sha256': images, 'PDF_skill_marker_successful_executions': 1,
        'post_render_change': 'Only two metadata-line trailing spaces removed; exact renderer metadata/body equivalence checked.'},
    'local_Lean_Lake_cache_or_Comparator_execution': False,
    'Git_commit_push_PR_or_campaign_count_change': False,
    'pending': 'Independent root publication/PDF review; later publication-commit and upstream PR checks.'}
dump(OUT / 'CHECKS.json', checks)
put_script = OUT / 'check_ke05_publication.py'
put_script.write_bytes(Path(__file__).read_bytes())
dump(OUT / 'MANIFEST.json', {'files': {p.name: digest(p) for p in sorted(OUT.iterdir()) if p.is_file() and p.name != 'MANIFEST.json'}})
print(json.dumps({'verdict': 'PREPARATION_CHECKS_PASS_READY_FOR_ROOT_REVIEW', 'protected_inputs': 149,
    'math_files': 23, 'tracked_changed_files': len(changed), 'local_links_checked': len(links),
    'pdf_pages': 4, 'pdf_sha256': digest(pdf), 'CHECKS_sha256': digest(OUT / 'CHECKS.json'),
    'MANIFEST_sha256': digest(OUT / 'MANIFEST.json')}, indent=2))

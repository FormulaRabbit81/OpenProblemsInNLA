"""Check the prepared MF-22 publication without running Lean or changing Git."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, sys

W = Path('/private/tmp/nla-lean-next-mf22-worktree')
P = W / 'matrix-functions-and-stability/MF-22/lean'
B = P / 'verification/publication-2026-09-16'
OUT = B / 'checks'
OUT.mkdir(exist_ok=True)
proof = 'c701bfeea660473fc31ad9d0c74b76309be3b49f'

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=W).decode()
def load(p): return json.loads(p.read_text())
def run(name, args):
    r = subprocess.run(args, cwd=W, capture_output=True, text=True)
    data = '$ ' + ' '.join(args) + '\n' + r.stdout + r.stderr + '\nEXIT_STATUS=' + str(r.returncode) + '\n'
    (OUT / (name + '.log')).write_text(data)
    assert r.returncode == 0, (name, data)
    return {'command': args, 'exit_code': r.returncode, 'log': name + '.log', 'sha256': digest(OUT / (name + '.log'))}

assert git('rev-parse', 'HEAD').strip() == proof
t = load(B / 'TRANSITION.json')
assert len(t['protected_inputs']) == 631
for rel, expected in t['protected_inputs'].items(): assert digest(P / rel) == expected, rel
for rel, expected in t['retained_original_manuscripts'].items(): assert digest(W / rel) == expected, rel
receipt = load(next((P / 'verification/linux-2026-09-16/artifacts/lean-MF-22').glob('verify-*/result.json')))
assert len(receipt['input_sha256']) == 634 and receipt['repository_commit'] == proof
for rel in t['metadata_updated']:
    assert digest(B / 'before/lean' / rel) == receipt['input_sha256'][rel], rel
old_page = (B / 'before/matrix-functions-and-stability/MF-22/README.md').read_text()
new_page = (P.parent / 'README.md').read_text()
assert old_page.split('## Statement\n', 1)[1] == new_page.split('## Statement\n', 1)[1]
assert '**Status:** Lean verified\n' in new_page and '**Last checked:** 2026-09-16' in new_page
assert 'does not certify this stronger linear estimate' in new_page
assert 'exponent **two**' in new_page
assert '634' in new_page and '35053254275' in new_page
for item in ['tools/lean', '.github/workflows/lean-verification.yml', 'docs/lean', 'problem_ids.json']:
    assert not git('diff', proof, '--', item).strip(), item
sources = load(P / 'ACTIVE-SOURCE-MANIFEST.json')['source_sha256']
assert len(sources) == 29
for rel, expected in sources.items(): assert digest(P / rel) == expected, rel
assert not [x for x in git('diff', '--name-only').splitlines() if x.endswith('.lean')]
assert not [x for x in git('ls-files', '--others', '--exclude-standard').splitlines() if x.endswith('.lean')]

# Every copied referee byte and bounded duplicate-audit byte is preserved.
referee_map = load(B / 'REFEREE-PATH-MAP.json')
for item in referee_map['files']: assert digest(P / item['retained']) == item['sha256'], item
dups = load(B / 'public-duplicate-audit/RETAINED-FILES.json')
for name, expected in dups['bounded_retained_files'].items(): assert digest(B / 'public-duplicate-audit' / name) == expected, name
assert load(B / 'PDF-SKILL-MARKER.json')['exit_code'] == 0

# Check all local links in the active publication reading path.
linked_files = [P.parent / 'README.md', P / 'README.md', P / 'SourceCorrespondence-current.md', P / 'reviews/final/README.md']
local_links = 0
git_resolved_sparse_links = []
for path in linked_files:
    for target in re.findall(r'\]\(([^)]+)\)', path.read_text()):
        if re.match(r'[a-zA-Z]+:', target) or target.startswith('#'): continue
        target = target.split('#', 1)[0]
        if not (path.parent / target).exists():
            assert path == P.parent / 'README.md' and '](' + target + ')' in old_page, (path, target)
            relative = (path.parent / target).resolve().relative_to(W)
            subprocess.run(['git', 'cat-file', '-e', proof + ':' + str(relative)], cwd=W, check=True)
            blob = subprocess.check_output(['git', 'cat-file', '-p', proof + ':' + str(relative)], cwd=W)
            git_resolved_sparse_links.append({'page': str(path.relative_to(W)), 'target': target, 'blob_sha256': hashlib.sha256(blob).hexdigest(), 'status': 'present in accepted Git commit; omitted only by sparse working-tree selection'})
        local_links += 1

changed = git('diff', '--name-only').splitlines()
allowed = {'CATALOG.md', 'README.md', 'RESOLVED.md', 'matrix-functions-and-stability/README.md', 'matrix-functions-and-stability/MF-22/README.md', 'matrix-functions-and-stability/MF-22/problem.tex', 'matrix-functions-and-stability/MF-22/problem.pdf', 'matrix-functions-and-stability/MF-22/lean/README.md', 'matrix-functions-and-stability/MF-22/lean/formalization.yaml', 'matrix-functions-and-stability/MF-22/lean/ACTIVE-SOURCE-MANIFEST.json', 'tools/render_problems.py'}
assert set(changed) == allowed, changed
new_files = git('ls-files', '--others', '--exclude-standard').splitlines()
assert all(f.startswith('matrix-functions-and-stability/MF-22/lean/') for f in new_files)
email_matches = []
for rel in changed + new_files:
    path = W / rel
    if path.suffix.lower() in {'.zip', '.pdf', '.png'}: continue
    for match in re.findall(r'[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', path.read_text(errors='replace')):
        email_matches.append((rel, match))
assert not email_matches, email_matches

commands = [
    run('manifest', [sys.executable, 'tools/lean/validate_manifest.py', 'matrix-functions-and-stability/MF-22/lean']),
    run('permanent-ids', [sys.executable, 'tools/validate_problem_ids.py', '--base-ref', 'origin/main']),
    run('permanent-id-tests', [sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v']),
    run('diff-check', ['git', 'diff', '--check']),
    run('pdf-info', ['pdfinfo', 'matrix-functions-and-stability/MF-22/problem.pdf']),
]
assert 'Pages:           3' in (OUT / 'pdf-info.log').read_text()

# The exact latest PDF and all three rendered pages were visually inspected.
inspection = Path('/tmp/nla-lean-next-20260915/mf22-publication-pdf-check')
pdf_sha = 'fedcea69bb72e94d2d3c3ef1e3722afe260b3083ef80325588f68338edbbf92f'
assert digest(P.parent / 'problem.pdf') == pdf_sha
page_hashes = {'page-1.png': '6a81ee49ad123dc1c7381920ca9558d95cad331395b7993669cf4cf0a5712f99', 'page-2.png': 'a922faba214dfb13534e7f21bbaf71be1f9ae1878125f7c86a8956d43f2343af', 'page-3.png': '2ba50cb62fbac5e2acb916b3ce93317da5f87655ef8835da5fadc84441622c28'}
for name, expected in page_hashes.items(): assert digest(inspection / name) == expected

checks = {
    'prepared_and_checked_by': '/root/mf22_publication_referee',
    'review_kind': 'publication-preparation self-check; independent root review remains required',
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'proof_commit': proof,
    'canonical_run': 35053254275,
    'all_631_prior_nonmetadata_inputs_unchanged': True,
    'all_29_implementation_file_hashes_unchanged': True,
    'all_original_canonical_target_bytes_from_statement_onward_unchanged': True,
    'original_informal_manuscripts_unchanged': True,
    'three_original_metadata_files_retained_exactly': True,
    'no_new_active_or_historical_dot_lean_files': True,
    'all_referee_files_retained_exactly': len(referee_map['files']),
    'bounded_duplicate_audit_preserved': True,
    'local_links_checked': local_links,
    'new_publication_links_all_resolve': True,
    'git_resolved_sparse_historical_links': git_resolved_sparse_links,
    'missing_publication_links': [],
    'contact_email_matches': [],
    'commands': commands,
    'changed_tracked_files': {rel: digest(W / rel) for rel in changed},
    'PDF': {'sha256': pdf_sha, 'pages': 3, 'visual_inspection': 'All three latest PNG pages inspected: readable mathematics, affiliations, scope distinctions and evidence; no clipping, overlap, missing glyphs or layout defects.', 'render_command': 'PANDOC=/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc python3 tools/render_problems.py MF-22', 'last_render_result': 'MF-22: OK; Rendered 1 problem documents.', 'rendered_page_sha256': page_hashes, 'PDF_skill_marker_count': 1},
    'whole_original_target_formalized_with_exponent': 2,
    'informal_linear_exponent_formalized': False,
    'no_local_Lean_Lake_or_cache_execution': True,
    'Git_commit_push_PR_performed': False,
    'publication_commit_and_its_Linux_execution': 'pending separate root review and execution',
}
(OUT / 'CHECKS.json').write_text(json.dumps(checks, indent=2) + '\n')
print(json.dumps({'verdict': 'publication preparation checks pass; ready for independent root review', 'CHECKS_sha256': digest(OUT / 'CHECKS.json'), 'protected_inputs': 631, 'source_files': 29, 'local_links': local_links, 'PDF_pages': 3}, indent=2))

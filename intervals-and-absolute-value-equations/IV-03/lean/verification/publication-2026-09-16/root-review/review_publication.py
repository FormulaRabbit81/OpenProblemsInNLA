"""Independent root review of IV-03's prepared publication transition."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, zipfile
B = Path('/tmp/nla-lean-next-20260915')
W = Path('/private/tmp/nla-lean-next-iv03-worktree')
REL = 'intervals-and-absolute-value-equations/IV-03/lean'
P = W / REL
HEAD = 'cef3e2f486285d0f6885231cda3ac2ff04c975cb'
O = P / 'verification/publication-2026-09-16/root-review'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def dump(p, x): p.write_text(json.dumps(x, indent=2) + '\n')
def git(*args): return subprocess.check_output(['git', '-c', 'gc.auto=0', *args], cwd=W)
assert not O.exists()
seal = W / '.iv03-publication-preparation/SEALED-PUBLICATION.json'
assert sha(seal) == '3b66ba143a1988cff403cda0eaf2aafc4089d2efb10640e1b2308d0c370b9dcc'
a = read(seal)
assert a['unchanged_HEAD'] == HEAD == git('rev-parse', 'HEAD').decode().strip()
assert len(a['project_inputs']) == 240 and len(a['changed_repository_documents']) == 8
for rel, h in a['project_inputs'].items(): assert sha(P / rel) == h, rel
for rel, h in a['changed_repository_documents'].items(): assert sha(W / rel) == h, rel
assert set(git('diff', '--name-only').decode().splitlines()) == set(a['changed_repository_documents']) | {REL + '/README.md', REL + '/formalization.yaml'}
for rel, h in read(P / 'PUBLICATION-MANIFEST.json')['files'].items(): assert sha(P / rel) == h, rel
t = read(P / 'verification/publication-2026-09-16/TRANSITION.json')
old = t['all140_accepted_inputs']
assert len(old) == 140
changed = []
for rel, h in old.items():
    assert hashlib.sha256(git('show', HEAD + ':' + REL + '/' + rel)).hexdigest() == h, rel
    if sha(P / rel) != h: changed.append(rel)
assert set(changed) == {'README.md', 'formalization.yaml'}
math = [rel for rel in old if rel.endswith('.lean') and (rel.startswith('NLA/') or rel in {'Solution.lean', 'Challenge.lean'})]
assert len(math) == 14 and all(sha(P / rel) == old[rel] for rel in math)
frozen = read(P / 'verification/linux-2026-09-16/mi04-independent/FROZEN-7-AND-STATEMENT-REVIEW-BINDINGS.json')
assert len(frozen['sha256']) == 7
for rel, h in frozen['sha256'].items(): assert sha(P / rel) == h, rel
marker = '## Problem statement'
before = git('show', HEAD + ':intervals-and-absolute-value-equations/IV-03/README.md').decode()
current = (P.parent / 'README.md').read_text()
assert before[before.index(marker):] == current[current.index(marker):]
checksdir = P / 'verification/publication-2026-09-16'
checks = read(checksdir / 'CHECKS.json')
assert sha(checksdir / 'CHECKS.json') == 'fba25e213586e73b1967d521b5f3e2bf3b6c7a2ac64d7e3f7a060aee444b4b87'
for rel, h in checks['original_manuscript_tex_and_pdf_unchanged'].items():
    assert sha(W / rel) == hashlib.sha256(git('show', HEAD + ':' + rel)).hexdigest() == h, rel
assert (W / 'problem_ids.json').read_bytes() == git('show', HEAD + ':problem_ids.json')
assert len(read(W / 'problem_ids.json')) == 217
copied = read(checksdir / 'checks/EXACT-RUNTIME-TRANSPORT.json')
assert len(copied) == 30
original = B / 'canonical-runs/IV03-35059255598'
for rel, h in copied.items():
    assert sha(P / 'verification/linux-2026-09-16' / rel) == sha(original / rel) == h, rel
assert checks['ID_tests_passed'] == 17
assert all(v['exit_code'] == 0 for v in checks['validator_commands'].values())
rx = re.compile(rb'[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
scanned = []
for rel in a['project_inputs']:
    if rel in old and rel not in changed: continue
    f = P / rel
    if f.suffix == '.zip':
        with zipfile.ZipFile(f) as z:
            for n in z.namelist(): assert not rx.search(z.read(n)), (rel, n)
    elif f.suffix != '.pdf': assert not rx.search(f.read_bytes()), rel
    scanned.append(rel)
pdf = P.parent / 'problem.pdf'
assert sha(pdf) == '6ba86f6e771a8c393d29af12f52456d19d7f3052dcaed04ba98a2e12be65c716'
pdftext = subprocess.check_output(['pdftotext', str(pdf), '-'])
assert not rx.search(pdftext)
for name in [b'Matthew J. Colbrook', b'Sidney Holden', b'George Stepaniants']:
    assert name in pdftext
pages = {str(n): sha(W / f'.iv03-publication-preparation/pdf-review-final/page-{n}.png') for n in range(1, 5)}
assert subprocess.run(['git', 'diff', '--check'], cwd=W, capture_output=True).returncode == 0
O.mkdir()
(O / 'REVIEW.md').write_text('''# IV-03 independent root publication review

Approve the exact prepared publication package for commit and a separate published-commit Linux run. Root independently reviewed the canonical and Lean README changes, complete formalization metadata, RESOLVED entry, all catalog/category changes and the IV-03-only renderer amendment. I visually inspected all four final PDF pages. They retain the original target, displayed matrix criterion, complete attribution and readable execution evidence without clipped text or formulas. The PDF hash and all inspected PNG hashes are recorded separately.

All240 prepared project inputs and eight changed repository documents match the preparer's sealed map. All140 accepted predecessors independently match their actual immutable Git blobs at cef3e2f486285d0f6885231cda3ac2ff04c975cb. Only README and formalization.yaml differ among them. All14 active mathematical Lean files, all seven frozen inputs, dependency pins, checker configuration, original reviews and accepted default Solution remain unchanged. All30 transported actual-run evidence files match the previously accepted original packet. This review is not a second Lean execution.

The docs correctly describe the full original two-sign equivalence and stronger n-squared negative-sign equivalence for every positive dimension and real closed entrywise interval. Zero widths, zero entries, reducible matrices and nonsymmetric endpoints remain allowed; no regularity premise is added. The original problem statement from its heading onward and the original mathematical TeX/PDF are byte-identical. Exact symbolic matrix algebra avoids numerical interval grids; LeanCert kernel-trust assertions are described without inventing an interval certificate.

Mathematical authorship remains Matthew J. Colbrook, Cambridge DAMTP. Formalization authorship remains Sidney Holden under Apache-2.0. George Stepaniants receives integration and verification credit with the Department of Computing and Mathematical Sciences, California Institute of Technology. AI assistance and the roles of source reviewers, publication preparer and actual runtime auditor are clear. The helper's fixed root label is not falsely counted as an extra executor. Newly added text, transported archives and PDF text passed independent contact-email screening.

The preparer's actual schema validator passed four declarations, permanent-ID validation passed217 IDs against the recorded origin/main, catalog generation passed and all17 ID tests passed. I read those logs and bound them to the sealed package rather than claim to have rerun them. The registry is unchanged. Only IV-03's evidence status changes in the generated indexes; aggregate counts reflect this isolated branch. The renderer changes only IV-03 page breaks and its verification-date footer. The four-page final PDF has no reported layout warnings.

The authenticated proof run35059255598 already accepted the exact proof/integration revision and all four exports, actual Comparator/default-kernel checks, LeanCert kernel trust, standard axioms and required per-project controls. The docs distinguish that run from earlier historical execution and later publication or upstream commits. No checker/platform infallibility, external human peer review or local macOS Lean execution is claimed. This approval changes no mathematical target or completed campaign count; the exact publication rerun and upstream submission remain separate gates.
''')
dump(O / 'CHECKS.json', {
    'reviewer': '/root', 'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': 'approve publication; actual published-commit run pending',
    'preparer_seal_sha256': sha(seal), 'proof_commit': HEAD,
    'all240_prepared_inputs_checked': True, 'all8_repository_documents_checked': True,
    'all140_previous_Git_inputs_checked': True, 'all138_nonmetadata_inputs_unchanged': True,
    'active14_unchanged': math, 'frozen7_unchanged': frozen['sha256'],
    'all30_runtime_files_exact': copied, 'original_target_and_manuscripts_unchanged': True,
    'registry217_unchanged': True, 'preparer_checks_read_and_bound_not_rerun': checks['validator_commands'],
    'all4_pdf_pages_visually_inspected': pages, 'pdf_sha256': sha(pdf),
    'new_or_changed_inputs_screened': scanned, 'no_new_contact_email': True,
    'source_edits_local_Lean_or_count_promotion': False})
(O / 'review_publication.py').write_bytes(Path(__file__).read_bytes())
dump(O / 'MANIFEST.json', {'files': {p.name: sha(p) for p in sorted(O.iterdir()) if p.is_file()}})
inputs = dict(a['project_inputs'])
for f in O.iterdir():
    if f.is_file(): inputs[str(f.relative_to(P))] = sha(f)
assert len(inputs) == 244
dump(B / 'IV03-ROOT-APPROVED-PUBLICATION.json', {
    'HEAD': HEAD, 'project': REL, 'project_files': inputs,
    'changed_repository_documents': a['changed_repository_documents'],
    'review_manifest_sha256': sha(O / 'MANIFEST.json'),
    'preparer_seal_sha256': sha(seal), 'input_count': 244,
    'publication_commit_and_run_pending': True})
print(json.dumps({name: sha(O / name) for name in ['REVIEW.md', 'CHECKS.json', 'MANIFEST.json']}, indent=2))
print('244 approved inputs; root record', sha(B / 'IV03-ROOT-APPROVED-PUBLICATION.json'))

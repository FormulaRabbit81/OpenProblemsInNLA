"""Prepare IV-03 publication documents only; never Lean, Git mutation, or publishing."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import zipfile
import yaml

W = Path('/private/tmp/nla-lean-next-iv03-worktree')
B = Path('/tmp/nla-lean-next-20260915')
ID = 'intervals-and-absolute-value-equations/IV-03'
problem = W / ID
P = problem / 'lean'
C = 'cef3e2f486285d0f6885231cda3ac2ff04c975cb'
R = B / 'canonical-runs/IV03-35059255598'
A = R / 'mi04-independent'
I = B / 'reviews/IV03-import-independent'
PUB = P / 'verification/publication-2026-09-16'
EMAIL = re.compile(rb'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-C', str(W), *args])

def put(p, value):
    value = value.encode() if isinstance(value, str) else value
    assert not EMAIL.search(value), f'Contact data requires omission: {p}'
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(value)

def dump(p, value):
    put(p, json.dumps(value, indent=2, ensure_ascii=False) + '\n')

assert git('rev-parse', 'HEAD').decode().strip() == C
assert not git('diff', '--name-only').strip()
assert not PUB.exists()
assert digest(A / 'MANIFEST.json') == 'c298268c7cd5d9dc791d123c79b5967ac9428df150b39091c34ea5257c8b2764'
assert digest(A / 'OPERATIONAL-CHECKS.json') == '7636c3f5cd5e41bac3613d2fbeadf268f392922e6d636124c95697accc0d10a4'
assert digest(I / 'MANIFEST.json') == 'e2db207327880290c916499a98ec9ac33053c3c1bcfa60d59a4d2c044e6b04b2'
receipt_path, = (R / 'artifacts/lean-IV-03').glob('verify-*/result.json')
receipt = json.loads(receipt_path.read_text())
assert receipt['repository_commit'] == C and receipt['result'] == 'comparator-accepted'
assert len(receipt['input_sha256']) == 140
for name, value in receipt['input_sha256'].items():
    assert digest(P / name) == value, name
metadata = ['README.md', 'formalization.yaml']
protected = {n: v for n, v in receipt['input_sha256'].items() if n not in metadata}
assert len(protected) == 138
original_page = (problem / 'README.md').read_text()
target = original_page.split('## Problem statement\n', 1)[1]
manuscript_path = 'references/colbrook-intervals-2026-09-11/manuscripts/IV-03.tex'
manuscript = {'path': manuscript_path, 'sha256': digest(W / manuscript_path)}
assert manuscript['sha256'] == 'f09cb222b822704855031d18c971b3d61dbea4a371ee4547414c9e40500c3e98'

# The PDF skill marker was executed successfully once immediately before this
# publication-authoring operation. Do not execute it again during rendering.
marker = Path('/Users/georgestepaniants/.codex/plugins/cache/openai-primary-runtime/pdf/26.909.22227/skills/pdf/container_tools/mark_artifact_operation_started.mjs')
dump(PUB / 'PDF-SKILL-MARKER.json', {
    'command': ['node', str(marker), '--operation-kind', 'edit', '--expected-output-count', '1', '--output-format', 'pdf'],
    'exit_code': 0, 'stdout': '', 'stderr': '', 'tool_chunk_id': '9e22b9',
    'executed_by': '/root/mi04_independent_referee', 'marker_sha256': digest(marker),
    'execution_note': 'Executed exactly once before the first publication-authoring command. Subsequent PDF rendering does not rerun this marker.'})
for name in metadata:
    put(PUB / 'before/lean' / name, (P / name).read_bytes())
for name in [ID + '/README.md', ID + '/problem.tex', ID + '/problem.pdf', 'RESOLVED.md', 'README.md', 'CATALOG.md', 'intervals-and-absolute-value-equations/README.md', 'tools/render_problems.py']:
    put(PUB / 'before' / name, (W / name).read_bytes())

# Supply only missing retained canonical metadata, byte-exactly from the existing
# tested Git object, so catalog tools can inspect all IDs. No sparse Git changes.
ids = json.loads((W / 'problem_ids.json').read_text())
missing = []
for name in sorted(set(ids.values()) | {str(Path(p).parent.parent / 'README.md') for p in ids.values()}):
    if not (W / name).exists():
        value = git('show', C + ':' + name)
        put(W / name, value)
        missing.append({'path': name, 'sha256': hashlib.sha256(value).hexdigest()})
dump(PUB / 'SPARSE-METADATA-MATERIALIZATION.json', {
    'source_commit': C,
    'scope': 'Only exact tracked canonical README and category-index bytes omitted by sparse checkout; no Git index, ref or configuration mutation.',
    'files': missing})

# Screen every retained source byte and every ZIP member before copying. No
# contact-bearing original manuscript duplicate is added; its immutable hash and
# upstream link are already retained in the import record.
privacy = []
for source in sorted(R.rglob('*')):
    if not source.is_file():
        continue
    if source.suffix == '.zip':
        with zipfile.ZipFile(source) as z:
            members = z.namelist()
            assert all(not EMAIL.search(z.read(n)) for n in members), source
        privacy.append({'path': str(source.relative_to(R)), 'sha256': digest(source), 'email_matches': 0, 'zip_members_screened': len(members)})
    else:
        assert not EMAIL.search(source.read_bytes()), source
        privacy.append({'path': str(source.relative_to(R)), 'sha256': digest(source), 'email_matches': 0})
shutil.copytree(R, P / 'verification/linux-2026-09-16')
runtime = P / 'verification/linux-2026-09-16'
put(runtime / 'source-lock.json', (W / 'tools/lean/source-lock.json').read_bytes())
dump(runtime / 'PRIVACY-SCREEN.json', {
    'scope': 'Every copied actual evidence file and all ZIP members screened before publication; no contact email found. No source bytes were redacted or silently changed.',
    'files': privacy})
dump(runtime / 'EXECUTION-PROVENANCE.json', {
    'actual_operational_reviewer': '/root/mi04_independent_referee',
    'shared_audit_legacy_reviewer_field': '/root',
    'explanation': 'The shared audit tool hard-codes /root. This child reviewer actually executed it and its own additional reconciliation. The fixed label does not establish another root execution or a second Lean run.',
    'report': 'mi04-independent/REVIEW.md', 'checks': 'mi04-independent/OPERATIONAL-CHECKS.json',
    'real_Lean_executor': 'GitHub non-root Linux runner, verify job 104675949451',
    'local_Lean_Lake_cache': False})
put(runtime / 'README.md', '''# IV-03 fresh canonical Linux execution

[Run 35059255598](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35059255598)
and [verify job 104675949451](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35059255598/job/104675949451)
passed at literal proof/integration commit
`cef3e2f486285d0f6885231cda3ac2ff04c975cb` on 16 September 2026 UTC.
The API head, raw checkout log and result receipt identify exactly that commit.
All four exports, LeanCert kernel-trust assertions, actual Comparator, Lean's
default-kernel replay, standard transitive axioms and required project controls passed.

The original ZIP, API records, job logs and all 13 extracted artifact members
are retained unchanged after contact screening. Artifact 10431667719 has SHA256
`65608be436508a0350c4d22e0e18f15e5e6706fc131f2e841707747f01e9a5e7`.
The receipt binds all **140** original project inputs: 139 entries inventoried
by the imported package manifest, plus the manifest itself. All fourteen active
Lean files, seven frozen inputs and both statement-review hashes are unchanged.
The conditional separate checker-controls job was skipped; all required
per-project controls actually ran inside the successful verification job.

The [independent operational audit](mi04-independent/REVIEW.md) read every
verification log and authenticated all inputs. Its retained manifest describes
paths relative to this runtime directory, as in the original sealed packet.
ROOT-AUDIT.json has a fixed reviewer=/root field, but its actual executor was
/root/mi04_independent_referee; [execution provenance](EXECUTION-PROVENANCE.json)
explains this. It does not establish an extra root execution or a second Lean run.
The fresh execution is separate from the retained historical run 34926260380.
No local macOS Lean run, later publication-commit success, upstream merge or
infallibility of GitHub/checker software is claimed.
''')

# Retain the complete independent import audit unchanged; its historical pending
# claims remain stage-specific, with current status described in the new index.
for source in sorted(I.rglob('*')):
    if source.is_file():
        put(P / 'reviews/campaign/import-review' / source.relative_to(I), source.read_bytes())
put(P / 'reviews/final/README.md', '''# IV-03 complete-source, import and runtime reviews

Two independent nonimplementing AI-agent campaign referees read the original
canonical target, complete Colbrook manuscript, all fourteen active Lean inputs,
all four contracts and all seven frozen inputs:

- [Elimination referee](../campaign/referee-elimination/REVIEW.md).
- [Matrix-inequalities referee](../campaign/referee-inequalities/REVIEW.md).

Both authenticated the historical Linux evidence. The [independent import
review](../campaign/import-review/REVIEW.md) reconciled 139 inventoried files plus
their package manifest, 140 actual inputs. Those historical reports preserve
their original stage-specific pending language. The subsequent fresh canonical
[runtime audit](../../verification/linux-2026-09-16/mi04-independent/REVIEW.md)
accepted real run 35059255598 at literal commit
`cef3e2f486285d0f6885231cda3ac2ff04c975cb`, binding all 140 inputs and actual
Comparator/default-kernel/axiom checks and required controls.

The inequalities referee subsequently prepared publication documents and
evidence without changing mathematical source; root publication review remains
separate. These reports use the repository's scoped Tau Ceti protocol. They are
AI-agent audits, not external human peer review, official Tau Ceti endorsement,
independent reruns by each referee or proof of checker/platform infallibility.
Original statement reviews and formalization reviews remain unchanged. Colbrook
retains mathematical authorship, Holden formalization credit and Apache-2.0,
and Stepaniants integration/verification credit with his Caltech department.
''')

# This coverage audit, unlike the earlier four-target audit, explicitly scanned
# IV-03 among the remaining canonical solved IDs and discovered Holden's source.
coverage = B / 'remaining-public-Lean-coverage-20260916'
names = ['REPORT.md', 'COVERAGE.json', 'TREE-CHECKS.json', 'IV03-SOURCE-FETCH.json', 'PR-TITLE-TRIAGE.json', 'MANIFEST.json', 'public-audit-inputs/HEADS.json', 'public-audit-inputs/SUMMARY.json', 'public-audit-inputs/MANIFEST.json']
for name in names:
    put(PUB / 'public-duplicate-audit' / name, (coverage / name).read_bytes())
dump(PUB / 'public-duplicate-audit/RETAINED-FILES.json', {
    'source_directory': str(coverage),
    'files': {name: digest(coverage / name) for name in names},
    'scope': 'Bounded coverage report, complete ID map, exact tree checks, IV-03 source provenance and public branch heads. Original manifests describe larger private/raw archives; this list describes the actual retained selection.'})
put(PUB / 'public-duplicate-audit/README.md', '''# Public duplicate-formalization audit and credited reuse

The campaign snapshot collected at 2026-09-16 04:04 UTC covered 14 public
repositories, 249 branch heads and 203 complete commit trees. A later complete
remaining-ID scan of those retained trees found IV-03 on Sidney Holden's branch
codex/lean-iv03 at `281f440650d174602120ca9b2b930d38f9fef205`. This submission
therefore reuses that Apache-2.0 formalization with its original credit. It does
not claim Stepaniants authored Holden's proof or Colbrook's mathematical argument.

The retained report is the original triage-stage account, before full-source
reviews and real runtime authentication. The complete source reviews, import
review and fresh canonical runtime acceptance are now linked in
[the review index](../../../reviews/final/README.md). The original earlier
four-target public-audit SUMMARY does not list IV-03; COVERAGE.json and REPORT.md
record the subsequent IV-03-inclusive scan over the same authenticated trees.

This audit does not exclude private, deleted, unpushed, later, unusually named
or otherwise undiscoverable work. It is a duplicate-work check, not a claim of
historical priority or a new literature search. Large raw trees and source
copies are not duplicated; RETAINED-FILES.json gives the actual public selection.
''')

section = r'''## Lean proof and verification evidence

**Mathematical argument: Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Formalization: Sidney Holden**, with OpenAI Codex assistance, under Apache-2.0. **Integration and verification submission: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. The [complete formalization at immutable revision cef3e2f4](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cef3e2f486285d0f6885231cda3ac2ff04c975cb/intervals-and-absolute-value-equations/IV-03/lean/Solution.lean) imports Holden's existing proof without changing its fourteen active Lean files.

The formal proof establishes the full original equivalence for **every positive dimension and every real closed entrywise interval**. In fact, the $`n^2`$ negative-sign vertices alone suffice, implying the original $`2n^2`$ two-sign criterion. Genuine invertibility and the signs of the actual inverse are included in the definition. Independent entries, zero widths, zero entries, reducible matrices, nonsymmetric endpoints and repeated vertices are all covered. No regularity or nonsingularity of the interval is assumed.

All **four declarations** are listed in [formalization.yaml](lean/formalization.yaml):

- `NLA.IV03.vertex_formula`: the pointwise vertices equal the stated matrix formula.
- `NLA.IV03.vertices_admissible`: every specified vertex belongs to the interval.
- `NLA.IV03.nSquaredCriterion`: the stronger negative-sign vertex equivalence.
- `NLA.IV03.twoSignCriterion`: the complete original two-sign equivalence.

The [independent Challenge](lean/Challenge.lean), [definitions](lean/NLA/IV03/Definitions.lean), [frozen numerical targets](lean/NUMERICAL_TARGETS.md) and [proof notes](lean/PROOF_NOTES.md) record the mathematical boundary. Exact maximum principles, principal and Schur closure, complementary minors, adjugate completion and a resolvent identity avoid numerical interval grids. The Solution closure excludes Challenge's deliberate specification placeholders. Complexity estimates are outside the formalized equivalence.

The project pins **Lean 4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. On **16 September 2026 UTC**, [Linux run 35059255598, verification job 104675949451](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35059255598/job/104675949451) checked literal proof/integration commit `cef3e2f486285d0f6885231cda3ac2ff04c975cb`. All four LeanCert kernel-trust assertions, Comparator statement checks and Lean default-kernel replay passed. Every exported theorem uses only `propext`, `Classical.choice` and `Quot.sound`. Required sandbox, rejection and checker controls ran inside the successful project job. [Actual logs and source hashes](lean/verification/linux-2026-09-16/README.md) bind all **140** candidate inputs.

Two independent AI-agent [complete-source reviews](lean/reviews/final/README.md), an [import review](lean/reviews/campaign/import-review/REVIEW.md), and an [audit of the fresh actual run](lean/verification/linux-2026-09-16/mi04-independent/REVIEW.md) support this record. These are distinct from external human peer review or a guarantee that GitHub/checker software is infallible. No local macOS Lean execution is claimed. The [project README](lean/README.md) gives `lake build Solution` and the shared Linux reproduction commands. Later publication and merge revisions require separate exact-commit checks; the named proof run does not certify a later revision.

The [bounded public duplicate audit](lean/verification/publication-2026-09-16/public-duplicate-audit/README.md) identified Holden's existing formalization, which is deliberately reused and credited here. The original mathematical manuscript, canonical target, source reviews, frozen inputs and license remain unchanged.

'''
updated = original_page.replace('**Status:** Solved', '**Status:** Lean verified', 1).replace('**Last checked:** 2026-09-11', '**Last checked:** 2026-09-16', 1)
old = 'This is agent verification, not external human peer review or formal proof-assistant certification.'
new = 'That original review was an informal agent review. The later Lean verification is recorded separately below; external human peer review is not claimed.'
assert old in updated and '## Lean proof and verification evidence' not in updated
updated = updated.replace(old, new, 1).replace('## Problem statement\n', section + '## Problem statement\n', 1)
assert updated.split('## Problem statement\n', 1)[1] == target
put(problem / 'README.md', updated)

archive = (W / 'RESOLVED.md').read_text()
start = archive.index('### IV-03 - Affirmative resolution')
end = archive.index('\n### ', start + 1)
entry = archive[start:end].replace('### IV-03 - Affirmative resolution', '### 🏆 IV-03 - Affirmative resolution with Lean verification', 1)
entry += '''**Lean verified, 16 September 2026 UTC. Mathematical argument: Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Formalization: Sidney Holden**, under Apache-2.0. **Integration and verification submission: George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. The [complete four-target formalization](intervals-and-absolute-value-equations/IV-03/lean/README.md) proves both vertex equivalences in every positive dimension without assuming regularity, retaining zero widths, zero entries and reducible cases. [Canonical Linux run 35059255598](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35059255598/job/104675949451) passed all four LeanCert kernel-trust assertions, Comparator statement checks, Lean default-kernel replay, standard transitive axioms and required controls at literal proof/integration commit `cef3e2f486285d0f6885231cda3ac2ff04c975cb`. Two independent AI-agent complete-source reviews and an authenticated fresh-run audit are retained. The fourteen active mathematical Lean inputs, frozen boundary and original manuscript are unchanged. See the [canonical evidence section](intervals-and-absolute-value-equations/IV-03/README.md#lean-proof-and-verification-evidence). This is not an external human peer-review claim; later publication and merge commits need their own checks.

'''
put(W / 'RESOLVED.md', archive[:start] + entry + archive[end:])

readme = (P / 'README.md').read_text()
start = readme.index('**The fresh campaign verification run is pending.**')
end = readme.index('\n\nStart with', start)
readme = readme[:start] + '''**Fresh canonical Linux verification passed for all four exports.**
[Run 35059255598, verify job 104675949451](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35059255598/job/104675949451)
checked literal proof/integration commit `cef3e2f486285d0f6885231cda3ac2ff04c975cb`
on 16 September 2026 UTC. LeanCert kernel-trust assertions, actual Comparator,
Lean's default-kernel replay, standard transitive axioms and all required
per-project rejection/isolation controls passed. The [actual evidence](verification/linux-2026-09-16/README.md)
and [independent runtime audit](verification/linux-2026-09-16/mi04-independent/REVIEW.md)
bind all 140 accepted inputs: 139 inventoried files plus their original manifest.

Two independent nonimplementing AI agents read the entire proof and original
target. Their [complete-source reports and later runtime record](reviews/final/README.md),
the [independent import review](reviews/campaign/import-review/REVIEW.md), and
the [historical run 34926260380](verification/historical-linux-34926260380/README.md)
remain available. The fresh execution is separate from that historical test.
The earlier import-stage pending prose, original package manifest and active
source inventory are preserved as historical evidence; they are not current
status declarations. The [publication transition](verification/publication-2026-09-16/TRANSITION.json)
updates only this README and formalization.yaml among the accepted inputs.
Later publication and merge revisions need separate exact-commit checks.''' + readme[end:]
readme += '''
The shared runtime helper hard-codes a /root reviewer field; the actual executor
was /root/mi04_independent_referee, as its retained execution provenance discloses.
The separate checker-controls workflow job was skipped for the unchanged harness;
every required per-project control ran inside the successful proof job. Reviewing
that real run does not establish a second independent execution by each referee,
and no claim of GitHub, runner or checker infallibility is made.
'''
put(P / 'README.md', readme)

y = yaml.safe_load((P / 'formalization.yaml').read_text())
assert y['project']['authors'] == ['Sidney Holden']
y['status']['scope'] = 'Complete affirmative answer for every positive dimension and every closed real entrywise interval, including zero widths, zero entries and reducible matrices, without a regularity premise. Both the stronger n-squared negative-sign and original two-sign equivalences are proved. All four exports passed actual fresh canonical Linux run 35059255598 at literal proof/integration commit ' + C + '. All fourteen active Lean inputs remain unchanged from Sidney Holden\'s existing formalization of Matthew J. Colbrook\'s mathematical argument. Complexity bounds are outside the formalized equivalence.'
y['status']['whole_problem_verified'] = True
for result in y['status']['main_results']:
    result['verification_status'] = 'Accepted by actual fresh non-root Linux run 35059255598 at literal commit ' + C + ': LeanCert kernel trust, Comparator statement matching, default-kernel replay, standard transitive axioms and required controls.'
y['review']['status'] = 'two independent complete-source campaign approvals; import approved; actual fresh canonical Linux execution and independent runtime audit accepted'
y['review']['notes'] += ' The later fresh run 35059255598 accepted all four exports and all required per-project controls at literal commit ' + C + '. The independent inequalities referee authenticated all 140 inputs and read all nine verification logs; see verification/linux-2026-09-16/mi04-independent/REVIEW.md. The fixed /root helper label is disclosed as that child\'s actual invocation. That referee subsequently prepared publication metadata only, with separate root publication review required. No additional independent Lean execution or checker/platform infallibility is claimed.'
y['repository']['note'] = 'Integration of Sidney Holden\'s unchanged Apache-2.0 formalization. Actual fresh canonical Linux run 35059255598 accepted literal proof/integration commit ' + C + '. No mathematical source or build configuration changes are introduced. Later publication and merge commits require separate exact-commit checks.'
y['alignment']['publication_evidence'] = 'PUBLICATION-ACCEPTANCE.json'
y['verification'] = {
    'proof_commit': C, 'verification_date_utc': '2026-09-16',
    'canonical_run': 'https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35059255598',
    'canonical_job': 'https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35059255598/job/104675949451',
    'canonical_inputs': 140, 'active_Lean_files': 14, 'solution_closure_files': 13,
    'frozen_inputs': 7, 'frozen_exports': 4, 'whole_problem_verified': True,
    'evidence': 'verification/linux-2026-09-16/README.md',
    'source_reviews': ['reviews/campaign/referee-elimination/REVIEW.md', 'reviews/campaign/referee-inequalities/REVIEW.md'],
    'fresh_runtime_audit': 'verification/linux-2026-09-16/mi04-independent/REVIEW.md',
    'executor_provenance': 'verification/linux-2026-09-16/EXECUTION-PROVENANCE.json',
    'default_target': 'Solution', 'transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'comparator': 'All four frozen statements accepted without definition substitutions; Lean default kernel accepted the complete Solution proof graph.',
    'LeanCert': 'Pinned kernel-trust verification module built; all four #assert_trust kernel assertions passed. Exact matrix algebra avoids interval computation.',
    'controls': 'All required sandbox, kernel, Comparator, sorry and native-rejection controls passed inside verify job 104675949451. Separate conditional checker-controls job skipped.',
    'local_Lean_execution': False,
    'later_publication_commit_execution': 'Separate; not claimed completed by this proof-run record.'}
put(P / 'formalization.yaml', '# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n' + yaml.safe_dump(y, sort_keys=False, allow_unicode=True, width=105))

dump(P / 'PUBLICATION-ACCEPTANCE.json', {
    'scope': 'Complete original all-dimensional inverse-M interval two-sign equivalence, with the stronger n-squared negative-sign criterion.',
    'mathematical_author': 'Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge',
    'formalization_author': 'Sidney Holden', 'license': 'Apache-2.0',
    'integration_and_verification_submitter': 'George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology',
    'proof_commit': C, 'run': 35059255598, 'job': 104675949451, 'date_utc': '2026-09-16',
    'artifact_id': 10431667719, 'artifact_sha256': digest(R / 'lean-IV-03.zip'),
    'receipt_sha256': digest(receipt_path), 'accepted_input_count': 140,
    'active_Lean_file_count': 14, 'frozen_input_count': 7, 'export_count': 4,
    'source_and_runtime_reviews': 'reviews/final/README.md',
    'actual_runtime_audit_sha256': digest(A / 'OPERATIONAL-CHECKS.json'),
    'actual_executor_disclosure': 'verification/linux-2026-09-16/EXECUTION-PROVENANCE.json',
    'actual_logs_and_receipt': 'verification/linux-2026-09-16',
    'transition': 'verification/publication-2026-09-16/TRANSITION.json',
    'protected_original_inputs': 138, 'changed_original_metadata': metadata,
    'later_commit_verification': 'pending separate exact-commit checking',
    'local_Lean_Lake_cache': False})

renderer = (W / 'tools/render_problems.py').read_text()
needle = '    if identifier == "MF-22":\n'
assert renderer.count(needle) == 1
renderer = renderer.replace(needle, '    if identifier == "IV-03":\n        # Separate verification evidence and keep the full original target together.\n        body = body.replace("## Lean proof and verification evidence\\n", "\\\\newpage\\n\\n## Lean proof and verification evidence\\n", 1)\n        body = body.replace("## Problem statement\\n", "\\\\newpage\\n\\n## Problem statement\\n", 1)\n' + needle, 1)
needle = 'if identifier in {"SP-04", "SP-05"}:\n            # These publication dates record formal verification'
assert renderer.count(needle) == 1
renderer = renderer.replace(needle, 'if identifier in {"SP-04", "SP-05", "IV-03"}:\n            # These publication dates record formal verification', 1)
put(W / 'tools/render_problems.py', renderer)

for name, value in protected.items():
    assert digest(P / name) == value, name
assert (problem / 'README.md').read_text().split('## Problem statement\n', 1)[1] == target
assert digest(W / manuscript_path) == manuscript['sha256']
for name in ['tools/lean', '.github/workflows/lean-verification.yml', 'docs/lean', 'problem_ids.json']:
    assert not git('diff', C, '--', name), name
dump(PUB / 'TRANSITION.json', {
    'prepared_by': '/root/mi04_independent_referee', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'proof_commit': C, 'proof_run': 35059255598, 'proof_job': 104675949451,
    'all140_accepted_inputs': receipt['input_sha256'], 'protected_inputs': protected,
    'protected_count': 138, 'metadata_updated': metadata,
    'all14_active_Lean_files_unchanged': True, 'all7_original_frozen_inputs_unchanged': True,
    'all_original_review_import_and_evidence_bytes_unchanged': True,
    'original_statement_from_problem_statement_heading_onward_unchanged': True,
    'retained_original_manuscript': manuscript,
    'original_source_MANIFEST_and_ACTIVE_SOURCE_MANIFEST_unchanged_historical_records': True,
    'renderer_change': 'IV-03-only evidence/statement page breaks and verification-date footer label',
    'sparse_metadata_materialization': 'SPARSE-METADATA-MATERIALIZATION.json',
    'duplicate_scope': 'public-duplicate-audit/README.md; existing Holden formalization reused and credited',
    'no_local_Lean_Lake_cache': True, 'Git_commit_push_PR': False,
    'publication_review_and_later_commit_execution': 'pending separate root review and exact-commit run'})
put(PUB / 'README.md', '''# IV-03 publication transition

Fresh canonical Linux run 35059255598 accepted literal proof/integration commit
`cef3e2f486285d0f6885231cda3ac2ff04c975cb`. This transition adds its actual
verification evidence, current status, attributed resolution entry and canonical
PDF/TeX. Among the 140 accepted project inputs, only README.md and
formalization.yaml are updated; all other 138 inputs remain byte-identical.
Those protected bytes include all fourteen active Lean files, all seven frozen
inputs, dependency/checker configuration, license, earlier reviews and evidence.
The original package MANIFEST.json and ACTIVE-SOURCE-MANIFEST.json are historical
snapshots; their pending prose is preserved and does not override the new record.
The publication manifest separately inventories the new complete project.

The exact before metadata and canonical documents are retained in before/.
The full original statement and Colbrook mathematical manuscript remain unchanged.
No contact-bearing duplicate of that manuscript is added. Colbrook retains
mathematical authorship with his Cambridge DAMTP affiliation; Holden retains
formalization credit and Apache-2.0; Stepaniants supplies integration and
verification, Department of Computing and Mathematical Sciences, Caltech.

The fresh runtime audit is an independent inspection of an actual GitHub Linux
execution, with the helper's legacy reviewer label explicitly explained.
Source reviewers are independent of the implementation. The inequalities referee
then prepared these publication documents without editing proof code or running
Lean, Lake or caches locally. No commit, push, PR or campaign count is made here.
Root publication review and any later exact-commit/merge execution are separate.
''')
print('Prepared IV-03 publication. Protected 138/140 original project inputs, all14 active Lean, frozen7, full original target and manuscript. No local Lean/Git publishing.')

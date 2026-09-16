"""Independent root review of the prepared MF-22 publication, without Lean."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import yaml

B = Path('/tmp/nla-lean-next-20260915')
W = Path('/private/tmp/nla-lean-next-mf22-worktree')
REL = 'matrix-functions-and-stability/MF-22/lean'
P = W / REL
V = P / 'verification/publication-2026-09-16'
OUT = V / 'root-review'
PROOF = 'c701bfeea660473fc31ad9d0c74b76309be3b49f'

def sha(data): return hashlib.sha256(data).hexdigest()
def digest(path): return sha(path.read_bytes())
def read(path): return json.loads(path.read_text())
def git(*args): return subprocess.check_output(['git', *args], cwd=W)

assert not OUT.exists(), 'Do not overwrite a sealed root review'
assert git('rev-parse', 'HEAD').decode().strip() == PROOF
t = read(V / 'TRANSITION.json')
c = read(V / 'checks/CHECKS.json')
assert digest(V / 'checks/CHECKS.json') == 'ee610a5e9ef76ac85a81eab9296a9b5b7dd45bea4f65211ddbf7c3b6245ab7ce'
assert digest(V / 'checks/REPORT.md') == 'b16dbd20bfd1d9fcbe068d95e76db36c5a6bf3066e3388b48010ad7f1a64a23c'
for name, expected in read(V / 'checks/MANIFEST.json')['files'].items():
    assert digest(V / 'checks' / name) == expected, name

receipt = read(next((P / 'verification/linux-2026-09-16/artifacts/lean-MF-22').glob('verify-*/result.json')))
inputs = receipt['input_sha256']
assert receipt['repository_commit'] == PROOF and len(inputs) == 634
git_paths = {s[len(REL)+1:] for s in git('ls-tree', '-r', '--name-only', PROOF, '--', REL).decode().splitlines()}
assert git_paths == set(inputs)
for name, expected in inputs.items():
    assert sha(git('show', PROOF + ':' + REL + '/' + name)) == expected, name
metadata = set(t['metadata_updated'])
assert metadata == {'README.md', 'formalization.yaml', 'ACTIVE-SOURCE-MANIFEST.json'}
assert t['protected_inputs'] == {k:v for k,v in inputs.items() if k not in metadata}
assert len(t['protected_inputs']) == 631
for name, expected in t['protected_inputs'].items():
    assert digest(P / name) == expected, name
for name in metadata:
    assert digest(V / 'before/lean' / name) == inputs[name]
for name, expected in t['retained_original_manuscripts'].items():
    assert digest(W / name) == expected == sha(git('show', PROOF + ':' + name))

active = read(P / 'ACTIVE-SOURCE-MANIFEST.json')
assert len(active['source_sha256']) == 29
for name, expected in active['source_sha256'].items():
    assert digest(P / name) == expected == inputs[name], name
cmp = read(P / 'comparator.json')
meta = yaml.safe_load((P / 'formalization.yaml').read_text())
assert [x['declaration'] for x in meta['status']['main_results']] == cmp['theorem_names']
assert len(cmp['theorem_names']) == 22 and cmp['definition_names'] == []
assert meta['status']['whole_problem_verified'] is True
assert all(x['sorry_count'] == 0 and set(x['axioms']) == set(cmp['permitted_axioms']) for x in meta['status']['main_results'])
assert meta['alignment']['source_correspondence'] == 'SourceCorrespondence-current.md'
assert all('35053254275' in x['verification_status'] and PROOF in x['verification_status'] for x in meta['status']['main_results'])
acceptance = read(P / 'PUBLICATION-ACCEPTANCE.json')
assert acceptance['proof_commit'] == PROOF and acceptance['canonical_run'] == 35053254275
assert acceptance['root_audit_sha256'] == digest(P / 'verification/linux-2026-09-16/ROOT-AUDIT.json')
for name, expected in acceptance['final_referees'].items():
    assert digest(P / name) == expected
for record in read(V / 'REFEREE-PATH-MAP.json')['files']:
    assert digest(P / record['retained']) == record['sha256']

old = git('show', PROOF + ':matrix-functions-and-stability/MF-22/README.md').decode()
new = (P.parent / 'README.md').read_text()
assert old.split('## Statement\n',1)[1] == new.split('## Statement\n',1)[1]
assert '**Status:** Lean verified' in new and 'exponent **two**' in new
assert 'does not certify this stronger linear estimate' in new
assert 'Department of Computing and Mathematical Sciences' in new
assert 'California Institute of Technology' in new
for path in ['problem_ids.json', 'tools/lean', '.github/workflows/lean-verification.yml', 'docs/lean']:
    assert not git('diff', PROOF, '--', path).strip(), path
for name, expected in c['changed_tracked_files'].items():
    assert digest(W / name) == expected, name
assert set(git('diff','--name-only').decode().splitlines()) == set(c['changed_tracked_files'])
new_files = git('ls-files','--others','--exclude-standard').decode().splitlines()
assert all(x.startswith(REL+'/') for x in new_files)
assert not any(x.endswith('.lean') for x in list(c['changed_tracked_files']) + new_files)

email_re = re.compile(r'[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
for name in list(c['changed_tracked_files']) + new_files:
    path = W / name
    if path.suffix.lower() not in {'.pdf','.zip','.png'}:
        assert not email_re.search(path.read_text(errors='replace')), name
for command in c['commands']:
    assert command['exit_code'] == 0
    assert digest(V/'checks'/command['log']) == command['sha256']
    assert (V/'checks'/command['log']).read_text().endswith('EXIT_STATUS=0\n')
assert c['new_publication_links_all_resolve'] and not c['missing_publication_links']
assert len(c['git_resolved_sparse_historical_links']) == 2
for record in c['git_resolved_sparse_historical_links']:
    path = (W/record['page']).parent/record['target']
    rel = path.resolve().relative_to(W)
    assert sha(git('show',PROOF+':'+str(rel))) == record['blob_sha256']
assert digest(P.parent/'problem.pdf') == 'fedcea69bb72e94d2d3c3ef1e3722afe260b3083ef80325588f68338edbbf92f'
for name, expected in c['PDF']['rendered_page_sha256'].items():
    assert digest(B/'mf22-publication-pdf-check'/name) == expected
assert not git('diff','--check').strip()

OUT.mkdir()
report = '''# MF-22 independent root publication review

The prepared publication is approved for commit, push and exact-publication-commit Linux verification. A new upstream PR and its execution remain subsequent steps; this review does not count MF-22 as submitted yet.

I independently reconciled all 634 accepted candidate inputs against literal Git commit c701bfeea660473fc31ad9d0c74b76309be3b49f and its authenticated receipt. All 631 protected nonmetadata inputs, all 29 mathematical files, the frozen contracts, dependency pins, Comparator configuration and shared checker are unchanged. The three original metadata inputs remain preserved before the documented update. The complete original canonical statement and all informal solution artifacts are unchanged.

I read the publication prose, formalization metadata, current source correspondence and renderer changes. The complete original existential polynomial target is proved with exponent two. The informal stronger exponent-one estimate is explicitly outside the formal claim. All 22 metadata results match the frozen Comparator exports and refer to the actual accepted proof execution. Source and runtime reviews are preserved byte-for-byte, with one authenticated execution independently audited by multiple agents distinguished from multiple independent executions.

I inspected all three rendered PDF pages; the mathematics, affiliation, original target and scope distinctions are readable without overlap or clipping. I checked the exact PDF and rendered-page hashes, sealed preparation logs, schema/target coverage, unchanged identity safeguards, generated catalog changes, contact-email absence and the two historical links omitted only by sparse checkout. The agent's actual schema, permanent-ID and 17-test results are preserved, not misrepresented as rerun by this review. I independently ran the source-reconciliation script and git diff --check. No local Lean/Lake/cache operation was performed.

George Stepaniants is credited with the Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematical attribution is preserved. No contact email was added. Later revision and upstream execution remain separately auditable gates.
'''
(OUT/'REVIEW.md').write_text(report)
(OUT/'review_publication_root.py').write_bytes(Path(__file__).read_bytes())
checks = {
 'reviewer':'/root', 'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'verdict':'APPROVE prepared publication; subsequent commit/runtime/PR pending',
 'proof_commit':PROOF, 'proof_run':35053254275,
 'all_literal_Git_and_receipt_inputs_reconciled':634,
 'all_protected_current_inputs_reconciled':631,
 'complete_mathematical_files_unchanged':29, 'frozen_targets':22,
 'full_original_target_and_informal_artifacts_preserved':True,
 'no_email_added':True, 'shared_checker_and_registry_unchanged':True,
 'publication_metadata_schema_and_tests':'agent execution independently bound; not rerun here',
 'root_PDF_visual_review_pages':3, 'root_diff_check_exit_code':0,
 'source_preparation_checks_sha256':digest(V/'checks/CHECKS.json'),
 'PDF_sha256':digest(P.parent/'problem.pdf'),
 'local_Lean_execution':False, 'publication_commit_execution_claimed':False,
 'changed_tracked_files':c['changed_tracked_files'],
}
(OUT/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
manifest={'scope':'Independent root publication review, without mathematical source changes or Lean execution',
          'files':{x.name:digest(x) for x in sorted(OUT.iterdir()) if x.is_file()}}
(OUT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'verdict':'APPROVED','root_review':str(OUT),'manifest_sha256':digest(OUT/'MANIFEST.json')},indent=2))

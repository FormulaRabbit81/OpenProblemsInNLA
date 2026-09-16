#!/usr/bin/env python3
"""Static integration, attribution, schema and evidence audit; no Lean execution."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import zipfile
import yaml

HERE = Path(__file__).resolve().parent
P = HERE.parents[1]
sha = lambda b: hashlib.sha256(b).hexdigest()
original = json.loads((HERE / 'ORIGINAL-75-INPUTS.json').read_text())
assert len(original) == 75
changed = []
original_lean_count = 0
protected = {}
for row in original:
    rel = row['path']
    current = P / rel
    assert current.is_file(), rel
    b = current.read_bytes()
    if sha(b) != row['sha256']:
        changed.append(rel)
        assert sha((HERE / 'before' / rel).read_bytes()) == row['sha256']
    else:
        protected[rel] = sha(b)
    if rel.endswith('.lean'):
        original_lean_count += 1
        assert sha(b) == row['sha256'], rel
assert changed == ['README.md', 'formalization.yaml']
assert len(protected) == 73
original_lean_paths = {r['path'] for r in original if r['path'].endswith('.lean')}
assert {str(f.relative_to(P)) for f in P.rglob('*.lean')} == original_lean_paths
freeze = json.loads((P / 'statement-freeze.json').read_text())
assert len(freeze['sha256']) == 7
for rel, expected in freeze['sha256'].items(): assert sha((P / rel).read_bytes()) == expected, rel
for rel, expected in freeze['reports'].items(): assert sha((P / rel).read_bytes()) == expected, rel
active = json.loads((P / 'ACTIVE-SOURCE-MANIFEST.json').read_text())
assert len(active['source_sha256']) == 14
for rel, expected in active['source_sha256'].items(): assert sha((P / rel).read_bytes()) == expected, rel
assert 'defaultTargets = ["Solution"]' in (P / 'lakefile.toml').read_text()

meta = yaml.safe_load((P / 'formalization.yaml').read_text())
assert meta['project']['authors'] == ['Sidney Holden']
assert meta['submission'] == {'author': 'George Stepaniants', 'role': 'integration and verification submission',
    'department': 'Department of Computing and Mathematical Sciences', 'university': 'California Institute of Technology'}
assert meta['sources'][1]['authors'] == ['Matthew J. Colbrook']
assert meta['project']['license'] == 'Apache-2.0'
assert meta['status']['whole_problem_verified'] is False
assert 'pending' in meta['status']['scope']
assert set(meta['status']['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
config = json.loads((P / 'comparator.json').read_text())
assert len(config['theorem_names']) == 4 and config['definition_names'] == []
assert {r['declaration'] for r in meta['status']['main_results']} == set(config['theorem_names'])
assert (P / 'Solution.lean').read_text().count('#assert_trust kernel') == 4
for ref in json.loads((P / 'reviews/campaign/RETAINED-REVIEW-BINDINGS.json').read_text()):
    root = P / ref['retained_directory']
    for rel, expected in ref['retained_files_sha256'].items(): assert sha((root / rel).read_bytes()) == expected
    assert sha((root / 'ORIGINAL-PACKET-MANIFEST.json').read_bytes()) == ref['original_complete_packet_manifest_sha256']

H = P / 'verification/historical-linux-34926260380'
archive = H / 'lean-IV-03.zip'
assert sha(archive.read_bytes()) == 'bef757bd594f82e327625b5bcbcc3c395e6d64e3764c95f926a25ffe95337177'
with zipfile.ZipFile(archive) as z:
    for item in z.infolist():
        if not item.is_dir(): assert (H / 'artifact' / item.filename).read_bytes() == z.read(item)
receipt_path = H / 'artifact/verify-20260915T034753Z-4053/result.json'
assert sha(receipt_path.read_bytes()) == '50494ef3df157aa2b69cdbc6c9f6a00d568be6d64e80678686be974f0393bfa7'
receipt = json.loads(receipt_path.read_text())
assert receipt['repository_commit'] == '516ad4a0e85c21c7ef34507db9ab3b68b393bb90'
assert receipt['result'] == 'comparator-accepted' and len(receipt['input_sha256']) == 75
old_bindings = json.loads((P / 'reviews/campaign/referee-elimination/ALL-75-INPUT-BINDINGS.json').read_text())
assert len(old_bindings) == 75
original_by_path = {r['path']: r for r in original}
for row in old_bindings:
    assert receipt['input_sha256'][row['path']] == row['tested_sha256']
    assert original_by_path[row['path']]['sha256'] == row['head_sha256']
identity = json.loads((H / 'API-IDENTITY-SUMMARY.json').read_text())
assert identity['actual_head_sha'] == receipt['repository_commit']
assert identity['repository'] == 'sidneyholden1/OpenProblemsInNLA'
assert identity['status'] == 'completed' and identity['conclusion'] == 'success'
assert len(identity['original_raw_API_sha256']) == 3
assert not list(P.rglob('run.json')) and not list(P.rglob('commit.json'))

email = re.compile(rb'[A-Za-z0-9_.+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
for f in P.rglob('*'):
    if f.is_file() and f.suffix != '.zip':
        assert not email.search(f.read_bytes()), ('contact-email pattern in package', str(f.relative_to(P)))
with zipfile.ZipFile(archive) as z:
    for name in z.namelist():
        if not name.endswith('/'): assert not email.search(z.read(name)), ('contact-email pattern in artifact', name)

validator = HERE / 'metadata-validator/tools/lean/validate_manifest.py'
schema = HERE / 'metadata-validator/docs/lean/schema/v0.4.schema.json'
assert sha(schema.read_bytes()) == '25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce'
command = [sys.executable, '-B', str(validator), str(P)]
proc = subprocess.run(command, capture_output=True, text=True)
(HERE / 'schema-validation.log').write_text(proc.stdout + proc.stderr + '\nEXIT_STATUS=' + str(proc.returncode) + '\n')
assert proc.returncode == 0, proc.stdout + proc.stderr

report = {
    'kind': 'IV-03 canonical integration package static audit',
    'reviewer_and_packager': '/root/ie13_continuation',
    'imported_revision': '281f440650d174602120ca9b2b930d38f9fef205',
    'original_inputs_fresh_Git_blob_verified': 75,
    'unchanged_original_inputs': 73,
    'changed_original_paths': changed,
    'original_changed_bytes_retained': True,
    'protected_original_paths_sha256': protected,
    'unchanged_original_Lean_files_including_historical_consumers': original_lean_count,
    'unchanged_active_Lean_inputs': 14,
    'unchanged_solution_closure': 13,
    'unchanged_frozen_inputs': 7,
    'unchanged_original_statement_freeze_and_reviews': True,
    'new_mathematical_files': 0,
    'all4_public_headers_unchanged_by_exact_source_equality': True,
    'build_configuration_changed': False,
    'default_target': 'Solution',
    'schema_v04_and_Comparator_coverage': 'PASS actual Python validation',
    'schema_validation_command': command,
    'schema_validation_log_sha256': sha((HERE / 'schema-validation.log').read_bytes()),
    'formalization_author': 'Sidney Holden',
    'mathematical_author': 'Matthew J. Colbrook',
    'integration_and_verification_submission_author': 'George Stepaniants',
    'department_and_university_published': True,
    'all_retained_reviews_match_sealed_sources': True,
    'historical_artifact_and_extracted_bytes_unchanged': True,
    'all75_historical_receipt_inputs_reconciled': True,
    'raw_contact_API_records_omitted': True,
    'contact_email_scan': 'No matches in package text or original artifact members',
    'fresh_campaign_Linux_run': 'pending',
    'local_Lean_or_Lake': False,
    'Git_branches_commits_push_PR_or_count_changes': False,
    'scope': 'Static packaging and metadata validation; no new proof execution. The two complete source/runtime reviews and original historical Linux evidence are retained. Root must independently review this package and run the exact integration commit.'
}
(HERE / 'PACKAGING-CHECKS.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': 'PASS static package checks', 'original_inputs': 75,
    'unchanged_active_Lean': 14, 'unchanged_all_original_Lean': original_lean_count,
    'unchanged_frozen': 7, 'new_math': 0, 'schema': 'PASS', 'fresh_run': 'pending',
    'checks_sha256': sha((HERE / 'PACKAGING-CHECKS.json').read_bytes())}, indent=2))

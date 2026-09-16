#!/usr/bin/env python3
"""Prepare attribution and bounded evidence without changing any Lean source."""
from pathlib import Path
import hashlib
import json
import shutil
import yaml

HERE = Path(__file__).resolve().parent
P = HERE.parents[1]
B = Path('/tmp/nla-lean-next-20260915')
OLD = B / 'reviews/IV03-ie13-independent'
sha = lambda b: hashlib.sha256(b).hexdigest()

def put(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2) + '\n')

def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)

original = json.loads((HERE / 'ORIGINAL-75-INPUTS.json').read_text())
prior = {r['path']: r for r in json.loads((OLD / 'ALL-75-INPUT-BINDINGS.json').read_text())}
assert len(original) == len(prior) == 75
for r in original:
    assert r['sha256'] == prior[r['path']]['head_sha256'], r['path']

d = yaml.safe_load((HERE / 'before/formalization.yaml').read_text())
d['project']['responsible_maintainers'] = ['George Stepaniants']
d['project']['affiliations'] = {'George Stepaniants': 'Department of Computing and Mathematical Sciences, California Institute of Technology'}
d['automation']['methods'][0]['prompting_notes'] = 'Reviewed numerical statements before proofs; two independent statement and final source referees; exact symbolic algebra to avoid interval computations; LeanCert trust and actual Linux Comparator required.'
d['automation']['notes'] = 'AI-assisted formalization prepared for Sidney Holden. George Stepaniants requested this subsequent integration and verification submission. Two additional independent nonimplementing agents reviewed all source bytes and historical runtime evidence. No human peer review, official Tau Ceti endorsement or source-author endorsement is claimed.'
d['status']['scope'] = 'Complete original affirmative answer for every positive dimension and every closed real entrywise interval, including zero widths, zero entries and reducible matrices, without a regularity premise. All four unchanged exports passed historical LeanCert kernel trust, Linux Comparator/default-kernel replay and actual rejection/sandbox controls at 516ad4a0e85c21c7ef34507db9ab3b68b393bb90 in run 34926260380. Two new complete independent source/history reviews approved the imported bytes. A fresh controlled execution on the eventual integration commit remains pending; this candidate does not promote a canonical status or completed count. Complexity bounds are not claimed formally.'
d['status']['whole_problem_verified'] = False
for result in d['status']['main_results']:
    result['verification_status'] = 'Authenticated historical Linux acceptance; fresh exact integration-commit run pending.'
d['review'] = {
    'status': 'two complete independent campaign source/history approvals; fresh campaign canonical run pending',
    'reviewers': ['OpenAI Codex agent /root/ie13_continuation', 'OpenAI Codex agent /root/mi04_independent_referee'],
    'notes': 'Original independent statement approvals, seven frozen inputs and final code reviews are preserved. All fourteen active Lean inputs and all four frozen headers are unchanged. The thirteen-file Solution closure excludes Challenge and historical consumer checks. Four deliberate Challenge placeholders establish no mathematics and are excluded from proof-development counts. The campaign reviewers separately authenticated the historical run; they did not launch a new proof execution.'}
d['acknowledgements'] = 'Original mathematical argument: Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Existing Lean formalization: Sidney Holden, Apache-2.0. Integration and verification submission: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, with OpenAI Codex assistance. Mathlib, LeanCert, Lean Comparator and formalization.yaml retain their implementation credit and licenses.'
d['repository'] = {'role': 'substantive-development',
    'note': "Integration of Sidney Holden's unchanged existing formalization. No new mathematical source or build configuration is introduced; fresh campaign Linux verification is pending.",
    'imported_revision': 'https://github.com/sidneyholden1/OpenProblemsInNLA/tree/281f440650d174602120ca9b2b930d38f9fef205/intervals-and-absolute-value-equations/IV-03/lean'}
d['submission'] = {'author': 'George Stepaniants', 'role': 'integration and verification submission',
    'department': 'Department of Computing and Mathematical Sciences', 'university': 'California Institute of Technology'}
d['alignment'] = {'numerical_boundary': 'NUMERICAL_TARGETS.md', 'proposed_statements': 'Challenge.lean',
    'implementation_entry': 'Solution.lean', 'source_correspondence': 'PROOF_NOTES.md',
    'campaign_import': 'verification/campaign-import-2026-09-16/TRANSITION.json'}
assert d['project']['authors'] == ['Sidney Holden']
(P / 'formalization.yaml').write_text('# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n' + yaml.safe_dump(d, sort_keys=False, allow_unicode=True, width=100))

common = ['REVIEW.md', 'CHECKS.json', 'ALL-75-INPUT-BINDINGS.json', 'ALL-14-SOURCE-BINDINGS.json',
          'ALL-4-HEADERS.json', 'ACTIVE-IMPORT-CLOSURE.json', 'LOG-AUTHENTICATION-CHECKS.json',
          'PRIMARY-API-BINDINGS.json']
review_bindings = []
for source_name, destination, expected_manifest in [
    ('IV03-ie13-independent', 'referee-elimination', 'f42adfe5217435f6688db6457c8ef1121798b94ba4214b03cb56654828338414'),
    ('IV03-mi04-independent', 'referee-inequalities', '898657375d14fc11c920b4d160deb3d827442074ccd2fa50b9b164c4f16d645e')]:
    src = B / 'reviews' / source_name
    dst = P / 'reviews/campaign' / destination
    assert sha((src / 'MANIFEST.json').read_bytes()) == expected_manifest
    files = common + (['CANONICAL-BINDINGS.json', 'HARNESS-BINDINGS.json'] if destination == 'referee-inequalities' else [])
    retained = {}
    for rel in files:
        copy(src / rel, dst / rel)
        retained[rel] = sha((src / rel).read_bytes())
    copy(src / 'MANIFEST.json', dst / 'ORIGINAL-PACKET-MANIFEST.json')
    review_bindings.append({'source_packet': source_name, 'retained_directory': str(dst.relative_to(P)),
        'original_complete_packet_manifest_sha256': expected_manifest, 'retained_files_sha256': retained,
        'scope': 'Bounded selection of the sealed full review. The original manifest records the full private review packet; it is not a manifest of this smaller selection.'})
put(P / 'reviews/campaign/RETAINED-REVIEW-BINDINGS.json', review_bindings)

run = OLD / 'authenticated-run'
H = P / 'verification/historical-linux-34926260380'
copy(run / 'lean-IV-03.zip', H / 'lean-IV-03.zip')
copy(run / 'job-104244928525.log', H / 'job-104244928525.log')
copy(run / 'FETCH-IDENTITY.json', H / 'FETCH-IDENTITY.json')
for src in sorted((run / 'artifacts/lean-IV-03').rglob('*')):
    if src.is_file(): copy(src, H / 'artifact' / src.relative_to(run / 'artifacts/lean-IV-03'))
meta = json.loads((run / 'run.json').read_text())
jobs = json.loads((run / 'jobs.json').read_text())
arts = json.loads((run / 'artifacts.json').read_text())
identity = {
    'kind': 'Derived contact-free identity summary of authenticated historical API responses; not a raw API response',
    'repository': meta['repository']['full_name'], 'run_id': meta['id'], 'run_url': meta['html_url'],
    'actual_head_sha': meta['head_sha'], 'status': meta['status'], 'conclusion': meta['conclusion'],
    'run_attempt': meta['run_attempt'], 'event': meta['event'],
    'jobs': [{k: job[k] for k in ['id', 'name', 'status', 'conclusion']} for job in jobs['jobs']],
    'artifacts': [{k: art[k] for k in ['id', 'name', 'size_in_bytes', 'digest', 'expired']} for art in arts['artifacts']],
    'original_raw_API_sha256': {name: sha((run / name).read_bytes()) for name in ['run.json', 'jobs.json', 'artifacts.json']},
    'raw_API_omitted': 'Raw run/commit API responses are not published because they may contain contact-email metadata. Original hashes and independently checked identity fields are retained. The artifact ZIP and log bytes are unchanged.'}
put(H / 'API-IDENTITY-SUMMARY.json', identity)

canonical_bindings = []
for rel in ['intervals-and-absolute-value-equations/IV-03/README.md', 'references/colbrook-intervals-2026-09-11/manuscripts/IV-03.tex']:
    raw = (OLD / 'canonical' / rel).read_bytes()
    retained = rel.endswith('README.md')
    if retained:
        copy(OLD / 'canonical' / rel, HERE / 'source-target' / rel)
    canonical_bindings.append({'path': rel, 'sha256': sha(raw),
        'source_commit': 'deb549fa9ddd6b119e6c59016f268237e645dfa2',
        'immutable_source_url': 'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/deb549fa9ddd6b119e6c59016f268237e645dfa2/' + rel,
        'copy_retained': retained,
        'note': 'Unchanged canonical snapshot.' if retained else 'Full original manuscript was read by both referees and remains unchanged upstream. The extra package copy is omitted because the document includes contact-email text; retain its exact binding and source link instead.'})
put(HERE / 'source-target/CANONICAL-TARGET-BINDINGS.json', canonical_bindings)
validator = Path('/tmp/nla-lean-next-ke05-worktree')
for rel in ['tools/lean/validate_manifest.py', 'docs/lean/schema/v0.4.schema.json',
            'docs/lean/schema/README.md', 'docs/lean/schema/LICENSE']:
    copy(validator / rel, HERE / 'metadata-validator' / rel)
put(HERE / 'metadata-validator/SOURCE.json', {
    'schema_source_commit': '99c678e569c7c4c0772db297c5ddd5e4c9b6322e',
    'schema_sha256': sha((validator / 'docs/lean/schema/v0.4.schema.json').read_bytes()),
    'validator_sha256': sha((validator / 'tools/lean/validate_manifest.py').read_bytes()),
    'scope': 'Metadata schema/coverage validation only; not a Lean checker.'})

freeze = json.loads((P / 'statement-freeze.json').read_text())
active = json.loads((OLD / 'ALL-14-SOURCE-BINDINGS.json').read_text())
for rel, expected in freeze['sha256'].items(): assert sha((P / rel).read_bytes()) == expected
for row in active: assert sha((P / row['path']).read_bytes()) == row['sha256']
put(P / 'ACTIVE-SOURCE-MANIFEST.json', {'original_source_commit': '281f440650d174602120ca9b2b930d38f9fef205',
    'source_sha256': {r['path']: r['sha256'] for r in active}, 'active_files': 14,
    'solution_closure_files': 13, 'fresh_campaign_run': 'pending', 'new_mathematical_files': 0})
transition = {
    'kind': 'Canonical integration candidate; no Git branch or new proof execution',
    'problem': 'IV-03', 'canonical_project_path': 'intervals-and-absolute-value-equations/IV-03/lean',
    'imported_repository': 'sidneyholden1/OpenProblemsInNLA',
    'imported_revision': '281f440650d174602120ca9b2b930d38f9fef205',
    'historically_tested_revision': '516ad4a0e85c21c7ef34507db9ab3b68b393bb90',
    'original_input_count': 75,
    'unchanged_original_paths': [r['path'] for r in original if r['path'] not in ['README.md', 'formalization.yaml']],
    'metadata_only_changed_paths': ['README.md', 'formalization.yaml'],
    'original_metadata_retained': {'README.md': 'before/README.md', 'formalization.yaml': 'before/formalization.yaml'},
    'all14_active_Lean_bytes_unchanged': True, 'all7_frozen_inputs_unchanged': True,
    'original_statement_freeze_unchanged': True, 'all_original_Lean_consumers_unchanged': True,
    'new_mathematical_files': 0, 'build_configuration_changed': False,
    'default_target': 'Solution', 'formalization_author': 'Sidney Holden',
    'mathematical_author': 'Matthew J. Colbrook',
    'integration_and_verification_submission_author': 'George Stepaniants',
    'submission_affiliation': 'Department of Computing and Mathematical Sciences, California Institute of Technology',
    'license': 'Apache-2.0', 'fresh_campaign_run': 'pending', 'new_local_Lean_or_Lake_run': False,
    'canonical_status_or_count_change': False,
    'historical_receipt': '../historical-linux-34926260380/artifact/verify-20260915T034753Z-4053/result.json',
    'review_binding_file': '../../reviews/campaign/RETAINED-REVIEW-BINDINGS.json',
    'historical_stage_note': 'NUMERICAL_TARGETS.md, SOURCE_PROVENANCE.json, statement freeze and original development receipts retain their original stage-specific wording. This transition and current README distinguish historical completion from the pending fresh campaign verification.'}
put(HERE / 'TRANSITION.json', transition)
print(json.dumps({'original_inputs': 75, 'unchanged_original_paths': 73,
    'all14_active_and_all7_frozen_unchanged': True, 'new_math': 0,
    'fresh_campaign_run': 'pending', 'package': str(P)}, indent=2))

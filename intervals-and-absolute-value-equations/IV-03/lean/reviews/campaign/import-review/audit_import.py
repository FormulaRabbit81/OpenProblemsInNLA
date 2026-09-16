#!/usr/bin/env python3
"""Independent read-only IV03 import audit. Writes only this referee packet."""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import re
import subprocess
import zipfile

B = Path('/tmp/nla-lean-next-20260915')
P = B / 'IV03-canonical-package'
I = P / 'verification/campaign-import-2026-09-16'
H = P / 'verification/historical-linux-34926260380'
O = Path(__file__).resolve().parent
W = Path('/private/tmp/nla-lean-next-iv03-worktree')
PROJECT = 'intervals-and-absolute-value-equations/IV-03/lean'
SOURCE = '281f440650d174602120ca9b2b930d38f9fef205'
TESTED = '516ad4a0e85c21c7ef34507db9ab3b68b393bb90'
EXPECTED = 'c80a3d70a83a478ddedd93e6badec0534cd5f8843a6e0fcc1d00117fbf518758'
assert not (O / 'MANIFEST.json').exists(), 'Sealed review: do not overwrite'

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()

def read(p):
    return json.loads(p.read_text())

def put(name, value):
    (O / name).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

def filemap(root):
    files = [q for q in root.rglob('*') if q.is_file()]
    assert not any(q.is_symlink() for q in root.rglob('*'))
    return {q.relative_to(root).as_posix(): sha(q.read_bytes()) for q in sorted(files)}

actual = filemap(P)
manifest = read(P / 'MANIFEST.json')
assert actual['MANIFEST.json'] == EXPECTED
assert len(actual) == 140 and len(manifest['files_sha256']) == 139
assert {k: v for k, v in actual.items() if k != 'MANIFEST.json'} == manifest['files_sha256']
assert filemap(W / PROJECT) == actual
put('ALL-140-PACKAGE-INPUTS.json', actual)

original = read(I / 'ORIGINAL-75-INPUTS.json')
original_paths = {x['path'] for x in original}
assert len(original) == len(original_paths) == 75
old = B / 'reviews/IV03-ie13-independent'
own = B / 'reviews/IV03-mi04-independent'
old_bindings = {x['path']: x for x in read(own / 'ALL-75-INPUT-BINDINGS.json')}
assert original_paths == set(old_bindings)
complete_tree = json.loads(gzip.decompress((B / f'public-duplicate-audit-20260916/trees/{SOURCE}.json.gz').read_bytes()))
assert complete_tree['truncated'] is False
published = {x['path'][len(PROJECT)+1:]: x for x in complete_tree['tree']
             if x['path'].startswith(PROJECT + '/') and x['type'] == 'blob'}
assert set(published) == original_paths
tree_bindings = read(I / 'SOURCE-TREE-BINDINGS.json')
trees = {}
for row in tree_bindings:
    raw = (I / 'source-trees' / (row['label'] + '.json')).read_bytes()
    assert sha(raw) == row['sha256']
    t = json.loads(raw)
    assert t['truncated'] is False and t['sha'] == row['returned_sha']
    trees[row['label']] = t
for parent, child, name in [('root', 'category', 'intervals-and-absolute-value-equations'),
                             ('category', 'problem', 'IV-03'), ('problem', 'project', 'lean')]:
    entries = {x['path']: x for x in trees[parent]['tree']}
    assert entries[name]['sha'] == trees[child]['sha']
project_blobs = {x['path']: x for x in trees['project']['tree'] if x['type'] == 'blob'}
assert set(project_blobs) == original_paths
reconciled = []
for row in original:
    rel = row['path']
    raw = (old / 'source' / rel).read_bytes()
    h = sha(raw)
    assert h == row['sha256'] == old_bindings[rel]['head_sha256']
    assert blob(raw) == row['Git_blob'] == published[rel]['sha'] == project_blobs[rel]['sha']
    assert len(raw) == row['bytes']
    assert row['source_commit'] == SOURCE
    assert row['immutable_source_url'].endswith('/' + SOURCE + '/' + PROJECT + '/' + rel)
    changed = rel in ['README.md', 'formalization.yaml']
    if changed:
        assert (I / 'before' / rel).read_bytes() == raw
        assert (P / rel).read_bytes() != raw
    else:
        assert (P / rel).read_bytes() == raw
    reconciled.append({'path': rel, 'source_sha256': h, 'source_Git_blob': blob(raw),
                       'package_sha256': actual[rel], 'metadata_change': changed,
                       'original_before_copy': 'verification/campaign-import-2026-09-16/before/' + rel if changed else None})
put('ORIGINAL-75-RECONCILIATION.json', reconciled)

active = read(own / 'ALL-14-SOURCE-BINDINGS.json')
assert len(active) == 14
for rel, row in active.items():
    assert actual[rel] == row['sha256']
    assert (P / rel).read_bytes() == (own / 'reviewed-source' / (rel + '.txt')).read_bytes()
assert read(P / 'ACTIVE-SOURCE-MANIFEST.json')['source_sha256'] == {k: v['sha256'] for k, v in active.items()}
freeze = read(P / 'statement-freeze.json')
assert len(freeze['sha256']) == 7
for rel, expected in {**freeze['sha256'], **freeze['reports']}.items():
    assert actual[rel] == expected
assert len([r for r in original_paths if r.endswith('.lean')]) == 21
put('ACTIVE-14-AND-FROZEN-7.json', {'active': active, 'freeze': freeze,
    'all_21_original_Lean_inputs_unchanged': True, 'all_build_configs_unchanged': True})

reviews = read(P / 'reviews/campaign/RETAINED-REVIEW-BINDINGS.json')
assert len(reviews) == 2
review_checks = []
for row in reviews:
    src = B / 'reviews' / row['source_packet']
    dst = P / row['retained_directory']
    raw = (src / 'MANIFEST.json').read_bytes()
    assert sha(raw) == row['original_complete_packet_manifest_sha256']
    assert (dst / 'ORIGINAL-PACKET-MANIFEST.json').read_bytes() == raw
    full = json.loads(raw)['files']
    for rel, h in full.items():
        assert sha((src / rel).read_bytes()) == h, (src, rel)
    for rel, h in row['retained_files_sha256'].items():
        assert sha((dst / rel).read_bytes()) == h == full[rel]
        assert (dst / rel).read_bytes() == (src / rel).read_bytes()
    assert len(filemap(dst)) == len(row['retained_files_sha256']) + 1
    review_checks.append({'source_packet': row['source_packet'],
        'original_manifest_sha256': sha(raw), 'full_private_packet_inputs_checked': len(full),
        'retained_report_and_binding_inputs': len(row['retained_files_sha256']) + 1,
        'all_retained_bytes_identical': True})
put('RETAINED-REVIEW-CHECKS.json', review_checks)

zip_bytes = (H / 'lean-IV-03.zip').read_bytes()
assert sha(zip_bytes) == 'bef757bd594f82e327625b5bcbcc3c395e6d64e3764c95f926a25ffe95337177'
assert zip_bytes == (own / 'runtime/lean-IV-03.zip').read_bytes()
assert (H / 'job-104244928525.log').read_bytes() == (own / 'runtime/job-104244928525.log').read_bytes()
with zipfile.ZipFile(H / 'lean-IV-03.zip') as z:
    members = {n: sha(z.read(n)) for n in z.namelist() if not n.endswith('/')}
    assert len(members) == 13
    assert filemap(H / 'artifact') == members
receipt = read(H / 'artifact/verify-20260915T034753Z-4053/result.json')
assert receipt['repository_commit'] == TESTED and receipt['result'] == 'comparator-accepted'
assert receipt['input_sha256'] == {k: v['tested_sha256'] for k, v in old_bindings.items()}
summary = read(H / 'API-IDENTITY-SUMMARY.json')
api = {n: read(own / 'fresh-api' / n) for n in ['run.json', 'jobs.json', 'artifacts.json']}
for n in api:
    assert summary['original_raw_API_sha256'][n] == sha((own / 'fresh-api' / n).read_bytes())
run = api['run.json']
assert summary['repository'] == run['repository']['full_name'] == 'sidneyholden1/OpenProblemsInNLA'
for key, rk in [('run_id','id'), ('run_url','html_url'), ('actual_head_sha','head_sha'),
                ('status','status'), ('conclusion','conclusion'), ('run_attempt','run_attempt'), ('event','event')]:
    assert summary[key] == run[rk]
assert summary['actual_head_sha'] == TESTED and summary['conclusion'] == 'success'
assert summary['jobs'] == [{k: j[k] for k in ['id','name','status','conclusion']} for j in api['jobs.json']['jobs']]
assert summary['artifacts'] == [{k: a[k] for k in ['id','name','size_in_bytes','digest','expired']} for a in api['artifacts.json']['artifacts']]
assert 'Derived contact-free' in summary['kind']
put('HISTORICAL-EVIDENCE-CHECKS.json', {'run': 34926260380, 'tested_commit': TESTED,
    'zip_sha256': sha(zip_bytes), 'artifact_members': members,
    'receipt_sha256': actual['verification/historical-linux-34926260380/artifact/verify-20260915T034753Z-4053/result.json'],
    'raw_job_sha256': actual['verification/historical-linux-34926260380/job-104244928525.log'],
    'derived_summary_matches_own_previously_fetched_API': True,
    'all_75_tested_inputs_match_previously_authenticated_receipt': True,
    'this_task_dispatched_or_executed_new_Lean': False})

canonical = read(I / 'source-target/CANONICAL-TARGET-BINDINGS.json')
previous_canonical = {x['path']: x for x in read(own / 'CANONICAL-BINDINGS.json')}
for row in canonical:
    rel = row['path']
    assert row['sha256'] == previous_canonical[rel]['sha256']
    private = (own / 'canonical' / (rel + '.txt')).read_bytes()
    assert sha(private) == row['sha256']
    if row['copy_retained']:
        assert (I / 'source-target' / rel).read_bytes() == private
    else:
        assert not (I / 'source-target' / rel).exists()
    seed_raw = subprocess.check_output(['git','show','HEAD:' + rel], cwd=W)
    assert seed_raw == private
put('CANONICAL-TARGET-CHECKS.json', canonical)

validator_files = ['tools/lean/validate_manifest.py','docs/lean/schema/v0.4.schema.json',
                   'docs/lean/schema/README.md','docs/lean/schema/LICENSE']
validator_bindings = {}
for rel in validator_files:
    data = (W / rel).read_bytes()
    assert data == (I / 'metadata-validator' / rel).read_bytes()
    assert data == subprocess.check_output(['git','show','HEAD:' + rel], cwd=W)
    validator_bindings[rel] = sha(data)
command = ['/tmp/nla-lean-formalization/venv/bin/python','-B','tools/lean/validate_manifest.py',PROJECT]
result = subprocess.run(command, cwd=W, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(O / 'actual-repository-validator.log').write_text(result.stdout)
assert result.returncode == 0 and 'PASS (4 declarations)' in result.stdout
put('VALIDATOR-CHECKS.json', {'command': command, 'cwd': str(W),
    'seed_commit': subprocess.check_output(['git','rev-parse','HEAD'],cwd=W,text=True).strip(),
    'actual_repository_validator_and_schema': validator_bindings, 'exit_code': result.returncode,
    'output_sha256': sha(result.stdout.encode()), 'Lean_or_Lake_run': False})

links = []
historical_prefixes = ['verification/campaign-import-2026-09-16/before/',
                       'verification/campaign-import-2026-09-16/source-target/']
for q in sorted(P.rglob('*.md')):
    rel = q.relative_to(P).as_posix()
    if rel in original_paths and rel != 'README.md':
        continue
    historic = any(rel.startswith(prefix) for prefix in historical_prefixes)
    for dest in re.findall(r'\]\(([^)]+)\)', q.read_text()):
        if dest.startswith(('https:','http:','#')):
            continue
        target = dest.split('#')[0].split('?')[0]
        exists = ((W / PROJECT / rel).parent / target).exists()
        assert exists or historic, (rel, dest)
        links.append({'source': rel, 'target': dest, 'resolves_in_intended_repository': exists,
                      'unchanged_historical_snapshot': historic})
assert (W / 'docs/lean/schema/v0.4.schema.json').is_file()
put('LINK-CHECKS.json', {'new_or_revised_local_links': links,
    'snapshot_note': 'Before copies and canonical-source snapshots preserve original text and relative paths. Those links are interpreted in their original location, not rewritten inside an evidence subdirectory. Their immutable source URLs are retained.',
    'new_current_documentation_broken_links': 0,
    'yaml_schema_relative_link_resolves_in_canonical_repository': True})

email = re.compile(rb"[A-Za-z0-9.!#$%&'*+/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?)+")
matches = []
for q in sorted(P.rglob('*')):
    if not q.is_file():
        continue
    if q.suffix == '.zip':
        with zipfile.ZipFile(q) as z:
            for name in z.namelist():
                if email.search(z.read(name)):
                    matches.append(q.relative_to(P).as_posix() + '::' + name)
    elif email.search(q.read_bytes()):
        matches.append(q.relative_to(P).as_posix())
assert not matches
put('PRIVACY-CHECKS.json', {'physical_inputs_scanned': len(actual), 'ZIP_members_scanned': len(members),
    'email_pattern_match_paths': matches, 'raw_run_jobs_artifact_API_responses_omitted': True,
    'extra_manuscript_copy_omitted_with_exact_binding_retained': True,
    'original_75_project_inputs_omitted': 0,
    'names_roles_departments_universities_preserved': True,
    'scope': 'Automated contact-pattern scan plus manual attribution/readme/metadata review; no claim of a universal privacy detector.'})

checks = {'reviewer': '/root/mi04_independent_referee', 'scope': 'independent canonical import package audit',
    'package_manifest_sha256': EXPECTED, 'manifest_entries': 139, 'physical_project_inputs_including_manifest': 140,
    'original_inputs': 75, 'original_inputs_unchanged': 73,
    'only_changed_original_inputs': ['README.md','formalization.yaml'],
    'active_mathematical_files_unchanged': 14, 'original_Lean_files_unchanged': 21,
    'frozen_files_unchanged': 7, 'selected_exports_unchanged': 4,
    'both_complete_source_reviews_preserved': True, 'whole_original_target_preserved': True,
    'actual_repository_metadata_validation': 'PASS (4 declarations)',
    'source_and_import_approval': True, 'fresh_exact_integrated_commit_runtime': 'pending',
    'local_Lean_or_Lake': False, 'Git_mutation_or_publication_or_count_change': False,
    'completed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
put('CHECKS.json', checks)
assert filemap(P) == actual and filemap(W / PROJECT) == actual
print(json.dumps(checks, indent=2))

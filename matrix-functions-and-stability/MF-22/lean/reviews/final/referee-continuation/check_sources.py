from pathlib import Path
import datetime, hashlib, json, re, subprocess
import yaml, jsonschema

B = Path('/tmp/nla-lean-next-20260915')
W = Path('/private/tmp/nla-lean-next-mf22-worktree')
R = Path(__file__).parent
rel = 'matrix-functions-and-stability/MF-22/lean'
P = W / rel
revision = 'c701bfeea660473fc31ad9d0c74b76309be3b49f'
sha = lambda b: hashlib.sha256(b).hexdigest()
filehash = lambda p: sha(p.read_bytes())
load = lambda p: json.loads(p.read_text())
def git(*args):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(W), *args])
assert git('rev-parse', 'HEAD').decode().strip() == revision
assert git('status', '--porcelain') == b''
active = load(P / 'ACTIVE-SOURCE-MANIFEST.json')['source_sha256']
accept = load(P / 'verification/DEVELOPMENT-ACCEPTANCE.json')
assert active == accept['accepted_source_sha256'] and len(active) == 29
run = B / 'development-runs/35052024095'
art = run / 'artifacts/lean-development-statements'
receipt = load(art / 'receipt.json')
meta = load(run / 'run.json')
assert receipt['repository_commit'] == accept['commit'] == meta['head_sha']
assert str(meta['id']) == receipt['run_id'] == '35052024095'
assert meta['status'] == 'completed' and meta['conclusion'] == 'failure'
assert receipt['uid'] == 1001 and receipt['platform'].startswith('Linux-')
assert receipt['comparator_run'] is False
for name, h in active.items():
    content = (P / name).read_bytes()
    assert sha(content) == h == sha(git('show', revision + ':' + rel + '/' + name)), name
    devname = 'NLA/MF22/Complete.lean' if name == 'Solution.lean' else name
    assert h == receipt['source_sha256'][devname]
    assert h == sha(git('show', accept['commit'] + ':.lean-development/' + devname))
    code = re.sub(r'/\-.*?\-/', '', content.decode(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b|#eval', code), name
    assert not re.search(r'^import .*Challenge', code, re.M), name
    if name != 'NLA/MF22/Definitions.lean':
        assert 'set_option leancert.trust "kernel"' in code, name
frozen = load(P / 'STATEMENT-FREEZE.json')
for name, h in frozen['frozen_files_sha256'].items():
    old = (P / 'statement-audit/snapshots' / name).read_bytes()
    assert sha(old) == h, name
    now = (P / name).read_bytes()
    if name == 'lakefile.toml':
        assert now == old.replace(b'defaultTargets = ["Challenge"]', b'defaultTargets = ["Solution"]')
    else:
        assert now == old, name
for item in frozen['reviews']:
    assert filehash(P / item['retained_path']) == item['sha256']
statement_tree = git('ls-tree', '-r', '--name-only',
    frozen['actual_linux_statement_run']['repository_commit'], '.lean-development/NLA/MF22').decode().splitlines()
assert statement_tree == ['.lean-development/NLA/MF22/Definitions.lean']
provenance = load(P / 'SOURCE-PROVENANCE.json')
for name, h in provenance['retained_sources_sha256'].items():
    assert filehash(P / name) == h
    canonical = 'matrix-functions-and-stability/MF-22/' + Path(name).name
    assert sha(git('show', provenance['source_commit'] + ':' + canonical)) == h
    assert filehash(W / canonical) == h
config = load(P / 'comparator.json')
exports = config['theorem_names']
assert len(exports) == 22 and len(set(exports)) == 22 and config['definition_names'] == []
permitted = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(config['permitted_axioms']) == permitted
challenge = (P / 'Challenge.lean').read_text()
assert len(re.findall(r'^\s*sorry\s*$', challenge, re.M)) == 22
implementation = load(P / 'IMPLEMENTATION-MAP.json')
assert {e['name'] for e in implementation['export_locations']} == {n.split('.')[-1] for n in exports}
for e in implementation['export_locations']:
    assert filehash(P / e['path']) == e['file_sha256']
    source = (P / e['path']).read_text()
    assert source.splitlines()[e['line'] - 1].startswith('theorem ' + e['name'] + ' ')
    pattern = r'^theorem ' + re.escape(e['name']) + r'\b(.*?)\s*:=\s*by'
    a = re.search(pattern, challenge, re.S | re.M)
    b = re.search(pattern, source, re.S | re.M)
    assert a and b and re.sub(r'\s+', ' ', a.group(1)).strip() == re.sub(r'\s+', ' ', b.group(1)).strip(), e['name']
commands = receipt['commands']
for c in commands:
    assert filehash(art / c['log']) == c['sha256']
    assert c['source_sha256_after'] == receipt['source_sha256']
for name, h in receipt['source_sha256'].items():
    assert sha(git('show', accept['commit'] + ':.lean-development/' + name)) == h, name
module = next(c for c in commands if c['log'] == 'MF-22-modules.log')
assert module['exit_code'] == 0
assert next(c for c in commands if c['log'] == 'MF-22-challenge.log')['exit_code'] == 0
log = (art / module['log']).read_text()
assert 'Build completed successfully' in log and not re.search(r'^error:', log, re.M)
tail = log[log.index('Built NLA.MF22.Complete'):]
measured = dict(re.findall(r"'(NLA\.MF22\.[^']+)' depends on axioms: \[([^\]]*)\]", tail))
assert set(measured) == set(exports)
for name, axioms in measured.items():
    assert set(axioms.split(', ')) == permitted
    assert set(accept['observed_axioms'][name]) == permitted
manifest = load(P / 'lake-manifest.json')
for dep in manifest['packages']:
    assert receipt['dependency_commits'][dep['name']] == dep['rev']
assert filehash(art / 'receipt.json') == accept['receipt_sha256']
assert filehash(run / 'ROOT-AUDIT.json') == accept['root_audit_sha256']
pack = load(P / 'verification/packaging/ROOT-CANDIDATE-CHECKS.json')
for name, h in pack['package_files_sha256'].items():
    assert filehash(P / name) == h, name
schema = load(W / 'docs/lean/schema/v0.4.schema.json')
metadata = yaml.safe_load((P / 'formalization.yaml').read_text())
jsonschema.validate(metadata, schema)
assert metadata['status']['whole_problem_verified'] is False
assert metadata['verification']['comparator'] == 'pending'
assert metadata['verification']['default_kernel'] == 'pending'
assert metadata['verification']['latest_development_run']['run_id'] == 35052024095
assert set(e['declaration'] for e in metadata['status']['main_results']) == set(exports)
assert metadata['project']['authors'] == ['George Stepaniants']
assert 'Department of Computing and Mathematical Sciences, California Institute of Technology' in metadata['project']['affiliations']['George Stepaniants']
assert b'George Stepaniants <>' in git('show', '--no-patch', '--format=%an <%ae>', revision)
out = {
    'reviewer': '/root/mf22_publication_referee',
    'reviewer_type': 'independent nonimplementing OpenAI Codex agent',
    'created_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'revision': revision,
    'full_implementation_files_read_by_reviewer': 29,
    'source_sha256': active,
    'full_original_statement_and_manuscript_read': True,
    'frozen_contracts_read_and_textually_equal_to_implementations': 22,
    'all_ten_statement_snapshots_verified': True,
    'only_active_frozen_configuration_change': 'Lake default target Challenge to Solution',
    'statement_commit_MF22_contains_only_Definitions': True,
    'package_hash_records_independently_verified': len(pack['package_files_sha256']),
    'development': {
        'run': 35052024095, 'revision': accept['commit'],
        'whole_workflow_conclusion': 'failure', 'MF22_complete_component_exit': 0,
        'full_component_log_read': True, 'log_sha256': filehash(art / module['log']),
        'receipt_sha256': filehash(art / 'receipt.json'),
        'all_Git_input_hashes_independently_checked': len(receipt['source_sha256']),
        'all_command_logs_hashed_and_sources_unchanged': len(commands),
        'measured_final_exports': 22, 'all_export_axioms': sorted(permitted),
        'platform': receipt['platform'], 'uid': receipt['uid'],
        'Comparator_run': False
    },
    'metadata_schema_valid': True,
    'metadata_sha256': filehash(P / 'formalization.yaml'),
    'schema_sha256': filehash(W / 'docs/lean/schema/v0.4.schema.json'),
    'statement_freeze_sha256': filehash(P / 'STATEMENT-FREEZE.json'),
    'review_scope': 'Complete mathematical source, current packaging, exact development evidence; canonical runtime approval deferred',
    'mathematical_source_verdict': 'approve',
    'canonical_runtime_verdict': 'pending',
    'local_Lean_or_Lake_executed': False,
    'published_PR_or_count_changed_by_reviewer': False
}
(R / 'CHECKS.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'verdict':out['mathematical_source_verdict'], 'source_files':29,
    'contracts':22, 'development_inputs':len(receipt['source_sha256']),
    'CHECKS_sha256':filehash(R / 'CHECKS.json')}, indent=2))

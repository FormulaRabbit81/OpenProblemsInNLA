"""Independent read-only SF01 publication-proposal audit; no execution claims.

Only this review directory is written. The sealed publication draft and current
worktree are read, not edited. Compiler/PDF/catalog/ID/runtime gates are separate.
"""
from pathlib import Path
import datetime
import hashlib
import importlib.metadata
import json
import re
import subprocess
import jsonschema

OUT = Path(__file__).resolve().parent
B = OUT.parent.parent
P = B / 'SF01-publication-private-35175258802'
W = Path('/private/tmp/nla-lean-next-sf01-worktree')
REL = 'matrix-functions-and-stability/SF-01/lean'
PAGE = 'matrix-functions-and-stability/SF-01/README.md'
HEAD = '3312b0795873cfecade03fa421a5433651d47674'
R = B / 'reviews/SF01-runtime-referee-35175258802'
PACKET = B / 'canonical-runs/SF01-35175258802'
bindings = {}
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    path = Path(path)
    data = path.read_bytes()
    bindings[str(path)] = sha(data)
    return data


def js(path):
    return json.loads(read(path))


def check(value, label):
    if not value:
        raise AssertionError(label)
    checks.append(label)


def blob(path):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(W), 'show', HEAD + ':' + path])


manifest_data = read(P / 'MANIFEST.json')
check(sha(manifest_data) == '054a69e207cd88e37f9ca535b30cf202e20860c016cb89991345d80b8e5791c8', 'exact sealed proposal identity')
manifest = json.loads(manifest_data)
check(set(manifest['files']) == {p.relative_to(P).as_posix() for p in P.rglob('*') if p.is_file() and p.name != 'MANIFEST.json'} | {p.relative_to(P).as_posix() for p in P.rglob('MANIFEST.json') if p != P / 'MANIFEST.json'}, 'complete private proposal inventory')
for p, digest in manifest['files'].items():
    check(sha(read(P / p)) == digest, 'proposal manifest entry ' + p)
t = js(P / 'TRANSITION.json')
check(t['proof_commit'] == HEAD and t['run'] == 35175258802 and t['job'] == 105055517720, 'proposal run and proof revision')
check(len(t['overlay']) == len(t['before']) == 36 and len(t['protected_original_inputs']) == 271 and len(t['protected_math_files']) == 37, '36 overlay paths and protected 271 inputs/37 sources')
actual_overlay = {p.relative_to(P / 'overlay').as_posix(): sha(read(p)) for p in (P / 'overlay').rglob('*') if p.is_file()}
check(actual_overlay == t['overlay'], 'all and only declared overlay bytes')
check(not any(p.is_symlink() for p in P.rglob('*')), 'ordinary nonsymlink proposal files')
for p, digest in t['before'].items():
    if digest is None:
        check(not (W / p).exists() and not (P / 'before' / p).exists(), 'declared new path ' + p)
    else:
        check(sha(read(P / 'before' / p)) == digest == sha(blob(p)) == sha(read(W / p)), 'exact original before bytes ' + p)
runtime_manifest_data = read(R / 'MANIFEST.json')
runtime_manifest_hash = sha(runtime_manifest_data)
check(runtime_manifest_hash == 'a2015c419716da0de1b13a0390d6fd5d0e1cb0d0ea2e5ee393bf393ab5551ffa' == t['independent_runtime_manifest_sha256'], 'independent runtime review seal')
runtime_manifest = json.loads(runtime_manifest_data)
for p, digest in runtime_manifest['files'].items():
    check(sha(read(R / p)) == digest, 'original runtime review payload ' + p)
receipt = js(PACKET / 'artifacts/lean-SF-01/verify-20260917T024125Z-3974/result.json')
check(receipt['input_sha256'] == t['protected_original_inputs'], 'all original protected inputs equal accepted execution receipt')
source = json.loads(blob(REL + '/verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json'))['accepted_source_sha256']
check(source == t['protected_math_files'], 'all37 protected mathematical bytes equal local/runtime acceptance')
allowed_existing_project_changes = {'README.md', 'formalization.yaml', 'PUBLICATION-EVIDENCE.json', 'reviews/INDEX.json'}
for p, digest in t['protected_original_inputs'].items():
    check(sha(blob(REL + '/' + p)) == digest == sha(read(W / REL / p)), 'original protected Git/worktree bytes ' + p)
    if REL + '/' + p in actual_overlay:
        check(p in allowed_existing_project_changes, 'only authorized existing project metadata overridden ' + p)
for p in source:
    check(REL + '/' + p not in actual_overlay, 'mathematical source absent from overlay ' + p)
check(not any(p.endswith('.lean') or p.startswith(('tools/', '.github/')) or p == 'problem_ids.json' for p in actual_overlay), 'no proof/config/checker/ID mutation proposed')
oldpage = read(P / 'before' / PAGE).decode()
newpage = read(P / 'overlay' / PAGE).decode()
marker = '<!-- colbrook-matrix-functions -->'
check(oldpage[oldpage.index(marker):] == newpage[newpage.index(marker):], 'complete original mathematical resolution and target suffix unchanged')
check(newpage.count('# SF-01 — ') == 1 and '**Status:** Lean verified' in newpage, 'same permanent page identity with explicit verified status')
oldresolved = read(P / 'before/RESOLVED.md').decode()
newresolved = read(P / 'overlay/RESOLVED.md').decode()
old_line = next(line for line in oldresolved.splitlines() if line.startswith('**SF-01 (Solved).**'))
new_line = next(line for line in newresolved.splitlines() if line.startswith('**SF-01 (Lean verified);'))
check(new_line.split('**', 2)[2] == old_line.split('**', 2)[2], 'RESOLVED original mathematical description unchanged')
prefix, suffix = oldresolved.split(old_line, 1)
check(newresolved.startswith(prefix + new_line) and newresolved.endswith(suffix), 'only SF01 resolved-entry expansion')
# The runtime packet is copied exactly, never reinterpreted as a new run.
runtime_dest = P / 'overlay' / REL / 'verification/linux-35175258802'
for name in ['ROOT-AUDIT.json', 'FETCH-IDENTITY.json', 'job-105055517720.log']:
    check(read(runtime_dest / name) == read(PACKET / name), 'unchanged original runtime evidence ' + name)
artifact_root = PACKET / 'artifacts/lean-SF-01'
for path in artifact_root.rglob('*'):
    if path.is_file():
        target = 'bootstrap/' + path.name if path.parent.name == 'bootstrap' else path.name
        check(read(runtime_dest / target) == read(path), 'unchanged artifact evidence ' + target)
check(read(runtime_dest / 'source-lock.json') == blob('tools/lean/source-lock.json'), 'unchanged source lock')
dest_review = P / 'overlay' / REL / 'reviews/canonical-runtime'
for path in R.iterdir():
    if path.is_file():
        check(read(dest_review / path.name) == read(path), 'byte-identical independent runtime review copy ' + path.name)
identity = js(runtime_dest / 'RUNTIME-IDENTITY.json')
for name, digest in identity['raw_API_sha256'].items():
    check(sha(read(PACKET / name)) == digest, 'omitted API digest preserved ' + name)
raw_run = js(PACKET / 'run.json')
check(identity['run'] == {k: raw_run[k] for k in identity['run']}, 'sanitized run identity preserves actual metadata')
raw_jobs = js(PACKET / 'jobs.json')['jobs']
check(identity['jobs'] == [{k: job[k] for k in identity['jobs'][i]} for i, job in enumerate(raw_jobs)], 'sanitized job identities preserve actual metadata')
check(identity['artifact_id'] == 10478074528 and identity['artifact_sha256'] == '3a459ec19dfdf960f4f0ec8e30f7ec249498b4b8f3a596b22be7783038e699c0', 'artifact identity remains exact')
# Parse YAML with installed Ruby Psych because this Python environment lacks
# PyYAML. Reject duplicate mapping keys/aliases, then run the installed Python
# JSON Schema implementation against the exact repository schema.
yaml_path = P / 'overlay' / REL / 'formalization.yaml'
ruby = """def walk(n)
  if n.is_a?(Psych::Nodes::Mapping)
    keys = n.children.each_slice(2).map { |k,v| k.value }
    raise 'duplicate YAML key' unless keys.uniq.length == keys.length
  end
  if n.respond_to?(:children) && n.children
    n.children.each { |c| walk(c) }
  end
end
s = File.read(ARGV[0]); walk(Psych.parse_stream(s))
puts JSON.generate(YAML.safe_load(s, aliases: false))
"""
parser_argv = ['/usr/bin/ruby', '-ryaml', '-rjson', '-e', ruby, str(yaml_path)]
metadata = json.loads(subprocess.check_output(parser_argv))
schema_path = W / 'docs/lean/schema/v0.4.schema.json'
schema = js(schema_path)
validator = jsonschema.validators.validator_for(schema)
validator.check_schema(schema)
validator(schema).validate(metadata)
checks.append('actual duplicate-key-safe YAML parse and v0.4 JSON Schema validation')
config = json.loads(blob(REL + '/comparator.json'))
results = metadata['status']['main_results']
check([r['declaration'] for r in results] == config['theorem_names'] and len(results) == 24, 'metadata exact ordered 24 frozen exports')
for result in results:
    data = read(W / REL / result['file'])
    check(sha(data) == result['file_sha256'] == receipt['input_sha256'][result['file']], 'declaration source hash ' + result['declaration'])
    name = result['declaration'].removeprefix('NLA.SF01.')
    check(re.match(r'^(?:theorem|lemma)\s+' + re.escape(name) + r'\b', data.decode().splitlines()[result['line'] - 1]), 'declaration line ' + result['declaration'])
    check(result['sorry_count'] == 0 and set(result['axioms']) == set(config['permitted_axioms']) and result['comparator_config'] == 'comparator.json', 'per-declaration trust metadata ' + result['declaration'])
    check(str(35175258802) in result['verification_status'] and HEAD in result['verification_status'], 'per-declaration actual run scope ' + result['declaration'])
check(metadata['status']['whole_problem_verified'] and metadata['verification']['canonical_verification_completed'], 'current metadata explicitly reports canonical proof acceptance')
check(metadata['project']['authors'] == ['George Stepaniants'] and 'California Institute of Technology' in metadata['project']['affiliations']['George Stepaniants'], 'required formalization authorship and affiliation')
check('publication document review pending' in metadata['review']['status'] and 'separate gates' in metadata['verification']['publication'], 'draft preserves unrun publication gates')
publication = js(P / 'overlay' / REL / 'PUBLICATION-EVIDENCE.json')
check(publication['proof_commit'] == HEAD and publication['canonical_run_id'] == 35175258802 and publication['canonical_job_id'] == 105055517720 and publication['submitted_input_count'] == 271, 'publication evidence exact executed proof identity')
index = js(P / 'overlay' / REL / 'reviews/INDEX.json')
check(index['canonical_runtime_reviews'][0]['manifest_sha256'] == runtime_manifest_hash, 'review index runtime manifest')
# Known current-state contradictions are recorded as required corrections;
# assertions about their presence do not count as approving those claims.
check(index['canonical_runtime'] == 'pending', 'recorded required correction: current runtime field remains stale')
check(index['current_complete_source_approval'].endswith('Current canonical runtime still pending.'), 'recorded required correction: current source-approval sentence remains stale')
pr = read(P / 'PR-BODY.md').decode()
check('DRAFT:' in pr and 'Replace this paragraph with measured results before posting.' in pr, 'planned PR checklist explicitly awaits completed gates')
spacing = []
pattern = re.compile(r'\b(?:all|All|contains|complete|Lean|Mathlib|LeanCert|UID|Theorem)\d')
for path in [P / 'PR-BODY.md', P / 'overlay/RESOLVED.md', yaml_path, runtime_dest / 'README.md']:
    for number, line in enumerate(read(path).decode().splitlines(), 1):
        if pattern.search(line):
            spacing.append({'path': path.relative_to(P).as_posix(), 'line': number, 'tokens': [m.group() for m in pattern.finditer(line)]})
check(bool(spacing), 'recorded required editorial spacing corrections')
contact_paths = []
email = re.compile(rb'(?<![A-Za-z0-9._%+-])[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
for path in (P / 'overlay').rglob('*'):
    if path.is_file() and email.search(read(path)):
        contact_paths.append(path.relative_to(P).as_posix())
check(not contact_paths and not email.search(read(P / 'PR-BODY.md')), 'no contact addresses introduced by overlay or planned PR')
# Bind the substantive review sources actually read for publication fidelity.
for path in ['NLA/SF01/Definitions.lean', 'NLA/SF01/NewtonConclusion.lean', 'SourceCorrespondence.md', 'REUSE-IV03.md', 'reviews/final/SF01-full-final-referee/REVIEW.md', 'reviews/historical/SF01-mf22-final-newton07/REVIEW.md', 'reviews/historical/SF01-mf22-routine-local11-14/REVIEW.md', 'reviews/historical/SF01-mf22-routine-local15/REVIEW.md']:
    check(sha(read(W / REL / path)) == receipt['input_sha256'][path], 'publication fidelity read source ' + path)
primary_path = B / 'next-statements/SF01-feasibility/source-private/SF-01.tex'
primary = read(primary_path)
check(sha(primary) == 'e9d14c133db5eeb58523efb4853a6d3bff43e955991cbbd7a67d082c0bb6cee8', 'complete original Colbrook manuscript read with contact-redacted display')
primary_blob = subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', str(W), 'show', 'ce47b5630bf3680d9211131c3a43825b022c139a:references/colbrook-matrix-functions-2026-09-11/manuscripts/SF-01.tex'])
check(primary == primary_blob, 'complete original manuscript literal upstream byte identity')
summary = {
    'reviewer': '/root/sf_ra_runtime_referee', 'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'role': 'Nonauthor of publication overlay; prior independent SF01/RA02 retained runtime-evidence referee. This is publication-document fidelity/source-continuation review, not another full proof or execution review.',
    'verdict': 'CONDITIONAL APPROVAL of sealed SF01 private publication proposal; exactly the two current INDEX state corrections and new-prose spacing remain required before final source approval.',
    'proposal_manifest_sha256': sha(manifest_data), 'proof_commit': HEAD,
    'passed_assertions': len(checks), 'external_bindings': len(bindings),
    'overlay_paths': 36, 'original_inputs_preserved_or_explicit_metadata_overrides': 271,
    'mathematical_sources_unmodified': 37, 'declaration_bindings': 24,
    'source_and_runtime_evidence_byte_continuation': True,
    'YAML_schema_validation': {'result': 'PASS', 'schema_sha256': sha(read(schema_path)), 'parser': 'Ruby Psych.safe_load; aliases disabled and duplicate mapping keys rejected', 'jsonschema_version': importlib.metadata.version('jsonschema')},
    'required_current_metadata_corrections': [
        'lean/reviews/INDEX.json canonical_runtime must identify actual accepted run35175258802 and its exact proof commit, instead of pending.',
        'lean/reviews/INDEX.json current_complete_source_approval must replace its trailing current-runtime-pending claim with the measured current proof-runtime acceptance; retain separate publication/upstream gates.'
    ],
    'required_spacing_corrections': spacing,
    'separate_remaining_gates': ['Follow-through of recorded final bounded metadata/spacing corrections', 'Replace draft PR checklist with completed measured results before posting', 'Root PDF rendering/visual inspection and catalog/permanent-ID validation', 'Actual exact publication-commit and upstream PR execution checks'],
    'no_contact_addresses_in_proposed_new_material': True,
    'no_Lean_Lake_Comparator_compiler_cache_PDF_catalog_ID_Git_mutation_publication_or_count_action': True,
    'limitations': ['No PDF was rendered or visually inspected by this referee.', 'No catalog or permanent-ID validator was run by this referee; no registry edit is in the proposal.', 'No later publication or upstream run is accepted by this review.', 'Full mathematical proof correctness remains in the separate source reviews; this review checks the new publication description against the original target and exact final declarations.']
}
for name, data in [('CHECKS.json', summary), ('ASSERTIONS.json', checks), ('SOURCE-BINDINGS.json', bindings)]:
    (OUT / name).write_text(json.dumps(data, indent=2, sort_keys=name == 'SOURCE-BINDINGS.json') + '\n')
print(json.dumps({'passed': True, 'assertions': len(checks), 'external_bindings': len(bindings), 'overlay_paths': 36, 'protected_inputs': 271, 'unchanged_math_sources': 37, 'exact_exports': 24, 'schema': 'PASS', 'required_index_corrections': 2, 'spacing_locations': len(spacing)}))

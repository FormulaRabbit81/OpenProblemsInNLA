"""Bounded RA02 publication review; no Git, compiler, PDF or network invocation.

Only this review directory is written. The proposal, raw sources, worktree and
earlier evidence remain read-only. Runtime checks are source continuations of
the separately sealed actual-evidence audit, not further proof executions.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import yaml

OUT = Path(__file__).resolve().parent
B = OUT.parent.parent
P = B / 'RA02-publication-private-35175272827'
W = Path('/private/tmp/nla-lean-next-ra02-worktree')
REL = 'randomized-and-low-rank-approximation/RA-02/lean'
BASE = 'randomized-and-low-rank-approximation/RA-02'
R = B / 'reviews/RA02-runtime-referee-35175272827'
PACKET = B / 'canonical-runs/RA02-35175272827'
HEAD = '26dc080e47b75a3aaf2e75fc2a282d0b8f4a4bbb'
RUN = 35175272827
JOB = 105055587640
PROPOSAL_SEAL = '2386eb322ef6467f32c034f41f7fe11e6971ada5e2b00ec5c4d4b83b60b429df'
RUNTIME_SEAL = 'e20cc614bb35d5909f95cfee6ddf9a7ea4cc1cfcfcf826d136f950dd8a20f5f5'
bindings = {}
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    path = Path(path).resolve()
    data = path.read_bytes()
    bindings[str(path)] = sha(data)
    return data


def js(path):
    return json.loads(read(path))


def check(condition, label):
    if not condition:
        raise AssertionError(label)
    checks.append(label)


def authenticate_manifest(folder, expected=None):
    data = read(folder / 'MANIFEST.json')
    if expected:
        check(sha(data) == expected, 'exact manifest ' + str(folder))
    manifest = json.loads(data)
    for path, digest in manifest['files'].items():
        check(sha(read(folder / path)) == digest, 'sealed payload ' + str(folder / path))
    return manifest


proposal = authenticate_manifest(P, PROPOSAL_SEAL)
check(set(proposal['files']) == {x.relative_to(P).as_posix() for x in P.rglob('*') if x.is_file() and x != P / 'MANIFEST.json'}, 'complete 318-file sealed proposal inventory')
check(len(proposal['files']) == 318 and not any(x.is_symlink() for x in P.rglob('*')), '318 ordinary sealed proposal files without symlinks')
author_bindings = js(P / 'BINDINGS.json')
for path, digest in author_bindings.items():
    check(sha(read(path)) == digest, 'publication author external binding ' + path)
t = js(P / 'TRANSITION.json')
check(t['proof_commit'] == HEAD and t['run'] == RUN and t['job'] == JOB, 'exact immutable accepted proof/run identity')
check(len(t['overlay']) == len(t['before']) == 44 and len(t['protected_original_inputs']) == 220 and len(t['protected_math_files']) == 35, 'complete overlay and original-input inventories')
overlay = {x.relative_to(P / 'overlay').as_posix(): sha(read(x)) for x in (P / 'overlay').rglob('*') if x.is_file()}
check(overlay == t['overlay'], 'all and only the 44 declared overlay paths')
for path, digest in t['before'].items():
    if digest is None:
        check(not (W / path).exists() and not (P / 'before' / path).exists(), 'new proposed path ' + path)
    else:
        check(sha(read(P / 'before' / path)) == digest == sha(read(W / path)), 'exact unchanged before snapshot and worktree ' + path)
check(not any(x.endswith('.lean') or x.startswith(('tools/', '.github/')) or x == 'problem_ids.json' for x in overlay), 'no proposed proof, checker, workflow, or ID-registry edit')
check(not any(x.endswith('.pdf') for x in overlay), 'no unrendered PDF represented as an overlay artifact')

authenticate_manifest(R, RUNTIME_SEAL)
for path, digest in js(R / 'SOURCE-BINDINGS.json').items():
    check(sha(read(path)) == digest, 'independent runtime-review source continuation ' + path)
git_inputs = js(R / 'GIT-INPUTS.json')
check(git_inputs['commit'] == HEAD and git_inputs['project'] == REL, 'prior authenticated Git-input map names the exact proof revision; no new Git invocation')
receipt_path = PACKET / 'artifacts/lean-RA-02/verify-20260917T024131Z-4243/result.json'
receipt = js(receipt_path)
check(receipt['input_sha256'] == t['protected_original_inputs'], 'all 220 protected input hashes equal the actual canonical receipt')
acceptance = js(W / REL / 'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json')
check(acceptance['accepted_source_sha256'] == t['protected_math_files'], 'all 35 protected mathematical sources equal local/runtime accepted map')
changed_project_docs = {'README.md', 'formalization.yaml', 'PUBLICATION-EVIDENCE.json', 'reviews/INDEX.json'}
check(set(t['changed_original_project_documents']) == changed_project_docs, 'only four existing project documents may be overridden')
for path, digest in t['protected_original_inputs'].items():
    check(sha(read(W / REL / path)) == digest, 'original accepted project input unchanged ' + path)
    if REL + '/' + path in overlay:
        check(path in changed_project_docs, 'existing project override limited to documentation ' + path)
for path, digest in t['protected_math_files'].items():
    check(REL + '/' + path not in overlay and sha(read(W / REL / path)) == digest, 'accepted mathematical source untouched ' + path)

# Authenticate the union on which the unchanged completed-manifest validator runs.
union = dict(t['protected_original_inputs'])
for path, digest in overlay.items():
    if path.startswith(REL + '/'):
        union[path[len(REL) + 1:]] = digest
static_project = P / 'static-validation/project'
static_files = {x.relative_to(static_project).as_posix(): sha(read(x)) for x in static_project.rglob('*') if x.is_file()}
check(static_files == union, 'static-validation project is precisely accepted inputs plus the proposed project overlay')
check(read(P / 'authoring/solution.tex') == read(P / 'overlay' / BASE / 'solution.tex'), 'standalone note authoring source equals proposed TeX')

# Original target and shared manuscript remain separately identified and intact.
source_provenance = js(W / REL / 'SOURCE-PROVENANCE.json')
email = re.compile(rb'(?<![A-Za-z0-9._%+-])[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}')
for record in source_provenance['source_records']:
    raw = read(record['raw_private_path'])
    packet = read(W / REL / record['packet_path'])
    check(sha(raw) == record['raw_sha256'] and sha(packet) == record['packet_sha256'], 'exact raw and reading-copy source digests ' + record['path'])
    check(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == record['raw_git_blob'], 'retained raw bytes match previously authenticated Git blob identity ' + record['path'])
    if record['contact_redaction_only']:
        redacted, count = email.subn(b'[contact omitted]', raw)
        check(count == record['contact_replacements'] == 1 and redacted == packet, 'reading manuscript differs solely by one contact-address replacement')
    else:
        check(raw == packet, 'unredacted original canonical target copy')
old_page = read(P / 'before' / BASE / 'README.md').decode()
new_page = read(P / 'overlay' / BASE / 'README.md').decode()
marker = '## Context and notation'
check(old_page[old_page.index(marker):] == new_page[new_page.index(marker):], 'complete original mathematical target and literature audit suffix preserved')
check(sha(old_page.split(marker + '\n', 1)[1].encode()) == t['original_target_suffix_sha256'], 'recorded original target suffix hash excludes its heading')
old_tex = read(P / 'before' / BASE / 'problem.tex').decode()
new_tex = read(P / 'overlay' / BASE / 'problem.tex').decode()
tex_marker = '\\subsection{Context and notation}'
check(old_tex[old_tex.index(tex_marker):] == new_tex[new_tex.index(tex_marker):], 'complete original canonical TeX target suffix preserved')
check(sha(old_tex.split(tex_marker, 1)[1].encode()) == t['original_problem_TeX_target_suffix_sha256'], 'recorded original TeX target suffix hash excludes its heading')
for label, text in [('old', old_page), ('new', new_page)]:
    check(text.startswith('# RA-02 — Polynomial trace-error factor after exactly the target rank of pivots'), 'permanent canonical title and ID ' + label)
old_resolution = old_page.split('**Negative resolution by Matthew J. Colbrook**', 1)[1].split('\n\n', 1)[0]
check('**Negative resolution by Matthew J. Colbrook**' + old_resolution in new_page, 'original mathematical resolution paragraph and author attribution preserved')
old_resolved = read(P / 'before/RESOLVED.md').decode()
new_resolved = read(P / 'overlay/RESOLVED.md').decode()
old_heading = '#### RA-02 — negative resolution'
new_heading = '#### RA-02 — Lean-verified negative resolution — formalization by George Stepaniants'
before, section = old_resolved.split(old_heading, 1)
old_section, after = section.split('\n#### RA-03', 1)
new_section = new_resolved.split(new_heading, 1)[1].split('\n#### RA-03', 1)[0]
check(new_resolved.startswith(before + new_heading) and new_resolved.endswith('\n#### RA-03' + after), 'RESOLVED changes limited to the RA02 entry')
check(new_section.startswith(old_section.rstrip() + '\n\n**Lean verified,'), 'original resolved mathematical paragraph remains intact before new formalization note')

# All copied runtime bytes equal the previously reviewed originals.
runtime_dest = P / 'overlay' / REL / ('verification/linux-' + str(RUN))
for name in ['ROOT-AUDIT.json', 'FETCH-IDENTITY.json', 'job-' + str(JOB) + '.log']:
    check(read(runtime_dest / name) == read(PACKET / name), 'unaltered original runtime evidence ' + name)
for path in (PACKET / 'artifacts/lean-RA-02').rglob('*'):
    if path.is_file():
        target = 'bootstrap/' + path.name if path.parent.name == 'bootstrap' else path.name
        check(read(runtime_dest / target) == read(path), 'unaltered actual artifact evidence ' + target)
check(read(runtime_dest / 'source-lock.json') == read(W / 'tools/lean/source-lock.json'), 'same accepted shared checker lock')
check(read(runtime_dest / 'COORDINATOR-ACCEPTANCE.json') == read(B / 'RA02-CANONICAL-ACCEPTANCE.json'), 'exact coordinator acceptance attachment')
for path in R.iterdir():
    if path.is_file():
        check(read(P / 'overlay' / REL / 'reviews/canonical-runtime' / path.name) == read(path), 'unaltered independent runtime report attachment ' + path.name)
identity = js(runtime_dest / 'RUNTIME-IDENTITY.json')
for path, digest in identity['raw_API_sha256'].items():
    check(sha(read(PACKET / path)) == digest, 'omitted actual API response digest ' + path)
raw_run = js(PACKET / 'run.json')
check(identity['run'] == {k: raw_run[k] for k in identity['run']}, 'sanitized run preserves exact API fields')
raw_jobs = js(PACKET / 'jobs.json')['jobs']
check(len(raw_jobs) == len(identity['jobs']) and identity['jobs'] == [{k: job[k] for k in identity['jobs'][i]} for i, job in enumerate(raw_jobs)], 'sanitized jobs preserve exact API fields')
check(identity['artifact']['id'] == 10477794322 and identity['artifact']['sha256'] == 'a475b2aeecd1d6224ad1b33aa6915858578a4ef6748a3f9f62eb8513fbf5134c', 'actual artifact ID and archive hash retained')

# Review scope and source-map continuation, without repeating full proof review.
index = js(P / 'overlay' / REL / 'reviews/INDEX.json')
for record in index['final_reviews']:
    folder = W / REL / Path(record['manifest']).parent
    authenticate_manifest(folder, record['manifest_sha256'])
for name, map_name in [('RA02-full-final-referee', 'SOURCE-MAP.json'), ('RA02-ie13-final-local-development19', 'SELECTED-SOURCE-PATHS.json')]:
    source_map = js(W / REL / 'reviews/final' / name / map_name)
    normalized = {('Solution.lean' if path == 'NLA/RA02/Complete.lean' else path): v['sha256'] for path, v in source_map.items()}
    check(normalized == t['protected_math_files'], 'complete nonauthor source-map continuation ' + name)
for record in index['statement_history']:
    folder = W / REL / Path(record['path']).parent
    authenticate_manifest(folder)
for record in index['current_attached_reviews']:
    authenticate_manifest(W / REL / Path(record['path']).parent, record['manifest_sha256'])
check(index['canonical_runtime']['proof_commit'] == HEAD and index['canonical_runtime']['run'] == RUN and index['canonical_runtime']['job'] == JOB and index['canonical_runtime']['manifest_sha256'] == RUNTIME_SEAL, 'current review INDEX identifies actual accepted runtime')
check('Two complete nonauthor source reviews accepted' in index['current_complete_source_approval'] and 'Pending' in index['publication_review'], 'current source acceptance and still pending separate publication review are explicit')
standards = js(W / REL / 'STANDARDS-PROVENANCE.json')
for record in standards['records']:
    check(sha(read(W / REL / record['packet_path'])) == record['sha256'], 'previously read pinned standards snapshot ' + record['packet_path'])
snapshots = {'README.md': REL + '/README.md', 'formalization.yaml': REL + '/formalization.yaml', 'PUBLICATION-EVIDENCE.json': REL + '/PUBLICATION-EVIDENCE.json', 'reviews/INDEX.json': REL + '/reviews/INDEX.json', 'canonical-README.md': BASE + '/README.md'}
for target, original in snapshots.items():
    check(read(P / 'overlay' / REL / 'verification/publication/before' / target) == read(P / 'before' / original), 'exact retained before-document snapshot ' + target)
original_math = js(P / 'overlay' / REL / 'verification/publication/ORIGINAL-MATHEMATICS.json')
check(original_math['raw_sha256'] == t['original_shared_mathematical_source_sha256'] == source_provenance['source_records'][1]['raw_sha256'] and original_math['contact_redacted_sha256'] == source_provenance['source_records'][1]['packet_sha256'], 'shared original mathematics identity stays distinct from the new formalization note')

# Actual repository metadata validation, using the fully authenticated union.
validator = P / 'static-validation/tools/lean/validate_manifest.py'
schema = P / 'static-validation/docs/lean/schema/v0.4.schema.json'
check(read(validator) == read(W / 'tools/lean/validate_manifest.py'), 'actual validator is unchanged repository code')
check(read(schema) == read(W / 'docs/lean/schema/v0.4.schema.json'), 'actual schema is unchanged pinned repository v0.4 schema')
argv = ['/Users/georgestepaniants/miniforge3/bin/python', '-B', str(validator), str(static_project)]
env = dict(os.environ)
env['PYTHONPATH'] = '/tmp/nla-publication-python-20260917'
env['PYTHONDONTWRITEBYTECODE'] = '1'
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
process = subprocess.run(argv, env=env, capture_output=True)
end = datetime.datetime.now(datetime.timezone.utc).isoformat()
log = process.stdout + process.stderr
(OUT / 'MANIFEST-VALIDATION.log').write_bytes(log)
check(process.returncode == 0 and b'Manifest schema and comparator coverage: PASS (27 declarations)' in log, 'actual unchanged repository validator PASS for all 27 proposed metadata entries')
validation = {'argv': argv, 'PYTHONPATH': env['PYTHONPATH'], 'PYTHONDONTWRITEBYTECODE': '1', 'started_at_utc': start, 'ended_at_utc': end, 'exit_code': process.returncode, 'log_sha256': sha(log), 'validator_sha256': sha(read(validator)), 'schema_sha256': sha(read(schema)), 'scope': 'Actual metadata validation only; no compiler or Comparator invocation.'}
(OUT / 'MANIFEST-VALIDATION.json').write_text(json.dumps(validation, indent=2) + '\n')
metadata = yaml.safe_load(read(P / 'overlay' / REL / 'formalization.yaml'))
config = js(W / REL / 'comparator.json')
results = metadata['status']['main_results']
check([entry['declaration'] for entry in results] == config['theorem_names'] and len(results) == 27, 'exact ordered 27 frozen exports in proposed metadata')
for entry in results:
    data = read(W / REL / entry['file'])
    check(sha(data) == entry['file_sha256'] == receipt['input_sha256'][entry['file']], 'actual source hash for metadata result ' + entry['declaration'])
    name = entry['declaration'].removeprefix('NLA.RA02.')
    check(re.match(r'^(?:theorem|lemma)\s+' + re.escape(name) + r'\b', data.decode().splitlines()[entry['line'] - 1]), 'actual declaration line for metadata result ' + entry['declaration'])
    check(entry['sorry_count'] == 0 and set(entry['axioms']) == set(config['permitted_axioms']) and entry['comparator_config'] == 'comparator.json', 'per-result trust and comparator metadata ' + entry['declaration'])
    check(str(RUN) in entry['verification_status'] and str(JOB) in entry['verification_status'] and HEAD in entry['verification_status'], 'per-result exact execution attribution ' + entry['declaration'])
check(metadata['status']['whole_problem_verified'] and metadata['verification']['canonical_verification_completed'] and metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0, 'complete-target metadata explicitly matches accepted proof status')
check(metadata['project']['authors'] == ['George Stepaniants'] and 'Department of Computing and Mathematical Sciences, California Institute of Technology' in metadata['project']['affiliations']['George Stepaniants'], 'required formalization author and affiliation')
check('publication overlay review pending' in metadata['review']['status'] and 'has not been applied, published or counted' in metadata['verification']['publication'], 'private proposal preserves current publication gate honestly')
check(metadata['toolchain']['lean'] == read(W / REL / 'lean-toolchain').decode().strip(), 'metadata exact pinned Lean version')
dependency_manifest = js(W / REL / 'lake-manifest.json')
for name, commit in metadata['toolchain']['dependencies'].items():
    check(next(x['rev'] for x in dependency_manifest['packages'] if x['name'] == name) == commit, 'metadata exact dependency pin ' + name)
publication = js(P / 'overlay' / REL / 'PUBLICATION-EVIDENCE.json')
check(publication['proof_commit'] == HEAD == publication['actual_checkout'] and publication['canonical_run_id'] == RUN and publication['canonical_job_id'] == JOB and publication['submitted_input_count'] == 220 and publication['contract_count'] == 27, 'publication evidence identifies only the accepted immutable execution')
check(publication['canonical_verification_completed'] and not publication['status_count_or_publication_change'] and len(publication['remaining_gates']) == 5, 'publication evidence keeps five future gates separate')

# Semantic source reads supporting this bounded document-fidelity review.
fidelity_reads = ['NLA/RA02/Definitions.lean', 'Challenge.lean', 'NLA/RA02/Numerical.lean', 'NLA/RA02/ExponentialComparison.lean', 'NLA/RA02/FinalCounterexample.lean', 'SourceCorrespondence.md', 'reviews/final/RA02-full-final-referee/REVIEW.md', 'reviews/final/RA02-ie13-final-local-development19/REVIEW.md']
for path in fidelity_reads:
    check(sha(read(W / REL / path)) == receipt['input_sha256'][path], 'read semantic publication source matches accepted input ' + path)
defs = read(W / REL / 'NLA/RA02/Definitions.lean').decode()
final = read(W / REL / 'NLA/RA02/FinalCounterexample.lean').decode()
check('∃ C : ℝ, 0 < C ∧ ∃ p : ℝ, 0 ≤ p ∧' in defs and '∀ n : ℕ, 1 ≤ n → ∀ A : Square n, ∀ hA : A.PosSemidef,' in defs and '∀ r : ℕ, 1 ≤ r → r ≤ n →' in defs, 'original constants/dimension/complex-PSD/rank quantifier order unchanged')
check('refine ⟨r + 1, by omega, arrowhead r, hA, r, hr, by omega, htail.1, ?_⟩' in final, 'reported order r+1 witness is the actual final proof construction')
check('theorem no_polynomial_trace_factor : ¬ PolynomialTraceFactor' in final, 'final export negates the complete original proposition')

pr = read(P / 'PR-BODY.md').decode()
check('DRAFT FOR THE COORDINATOR:' in pr and 'Replace this paragraph and the checklist below with measured final results before posting.' in pr, 'planned PR makes its outstanding measured-results gate explicit')
old_clause = 'the formal proof uses its disclosed finite arrowhead route.'
new_clause = 'the formal proof uses the separately documented finite arrowhead route, an alternative proof of the same negative answer.'
check(pr.count(old_clause) == 1, 'record the one requested PR attribution clarification')
corrections = [{'path': 'PR-BODY.md', 'before_sha256': sha(pr.encode()), 'old_text': old_clause, 'required_replacement': new_clause, 'reason': 'The preceding subject is the original manuscript; the finite arrowhead construction is explicitly an alternative in frozen SourceCorrespondence and differs from the manuscript lower-triangular sharp-limit family. Clarify the antecedent without changing any proof or accepted mathematical claim.'}]
(OUT / 'REQUIRED-CORRECTIONS.json').write_text(json.dumps(corrections, indent=2) + '\n')
for path in list((P / 'overlay').rglob('*')) + [P / 'PR-BODY.md']:
    if path.is_file():
        check(not email.search(read(path)), 'no contact address in proposed publication file ' + path.relative_to(P).as_posix())

summary = {'reviewer': '/root/sf_ra_runtime_referee', 'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'verdict': 'CONDITIONAL APPROVAL of the complete RA02 publication overlay: one planned-PR attribution clarification remains; no proof or mathematical-target correction is requested.', 'scope': 'Independent publication-document fidelity and source/evidence continuation; prior runtime referee, nonauthor of this overlay. No new full proof review, Git, compiler, Lean, Comparator, PDF, catalog, publication or count action.', 'proposal_manifest_sha256': PROPOSAL_SEAL, 'proof_commit': HEAD, 'runtime_run': RUN, 'runtime_job': JOB, 'runtime_review_manifest_sha256': RUNTIME_SEAL, 'proposal_inventory': 318, 'author_external_bindings_reauthenticated': len(author_bindings), 'overlay_paths': 44, 'protected_original_inputs': 220, 'unchanged_mathematical_sources': 35, 'exact_metadata_exports': 27, 'authenticated_static_union_files': len(union), 'assertions_passed': len(checks), 'external_bindings': len(bindings), 'actual_metadata_validator': validation, 'required_corrections': corrections, 'remaining_separate_gates': ['Bounded follow-through of the one planned PR attribution clarification', 'Record this review and its follow-through in current publication metadata without rewriting historical reviews', 'Render and visually inspect both PDFs', 'Catalog and permanent-ID safeguards against the published base', 'Replace draft PR paragraph/checklist with measured results before posting', 'Actual exact publication-commit and upstream PR checkout verification'], 'raw_sources_untouched': True, 'no_Git_network_compiler_Lean_Lake_Comparator_cache_PDF_catalog_ID_worktree_publication_count_mutation': True}
for name, value in [('CHECKS.json', summary), ('ASSERTIONS.json', checks), ('SOURCE-BINDINGS.json', bindings)]:
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=name == 'SOURCE-BINDINGS.json') + '\n')
print(json.dumps({'passed': True, 'assertions': len(checks), 'external_bindings': len(bindings), 'overlay_paths': 44, 'protected_inputs': 220, 'unchanged_mathematical_sources': 35, 'exact_exports': 27, 'metadata_validator': 'PASS', 'required_PR_clarifications': 1}))

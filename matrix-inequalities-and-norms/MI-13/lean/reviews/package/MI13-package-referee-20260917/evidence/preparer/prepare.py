"""Prepare canonical MI13 sources from an actually successful local run.

No compiler, Git mutation, network call, or success-count change is performed.
The resulting package still needs two final review acceptances and Linux checks.
"""
from pathlib import Path
import datetime, difflib, hashlib, json, re, shutil
import yaml

B = Path('/private/tmp/nla-lean-next-20260915')
L = Path('/private/tmp/nla-lean-local-shared-20260916')
S = B / 'next-proofs/MI-13'
P = B / 'MI13-canonical-package-local53'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
EMAIL = re.compile(rb'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
retained = []

def put(rel, data):
    if isinstance(data, str):
        data = data.encode()
    assert not EMAIL.search(data), rel
    p = P / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data)

def dump(rel, data):
    put(rel, json.dumps(data, indent=2, ensure_ascii=False) + '\n')

def copy(p, rel):
    p = Path(p)
    put(rel, p.read_bytes())
    retained.append({'original_path': str(p), 'path': rel, 'sha256': sha(p)})

def main():
    report = read(B / 'MI13-LOCAL-COMPLETE-53.json')
    assert sha(B / 'MI13-LOCAL-COMPLETE-53.json') == '22930d6b38d589b7fe194746bc5f5ea4ecfc531c0dc0bb4c5916bf06fcdfd4cc'
    receipt = read(report['receipt'])
    assert sha(report['receipt']) == report['receipt_sha256']
    assert receipt.get('end') and not receipt['failed_modules'] and not receipt['blocked_modules']
    sources = report['sources']
    assert len(sources) == 22 and report['fresh_MI13_warnings'] == 0
    cfg = read(S / 'comparator.json')
    assert len(cfg['theorem_names']) == 36 and set(report['observed_axioms']) == set(cfg['theorem_names'])
    freeze = read(S / 'STATEMENT-FREEZE.json')
    assert sha(S / 'STATEMENT-FREEZE.json') == 'bddc9d048f92e28dd8912f9bfb8293e12f07f2458fe7fb5a77e5b3c57e16e732'
    assert len(freeze['frozen_files']) == 13
    for rel, digest in {**sources, **freeze['frozen_files']}.items():
        assert sha(S / rel) == digest, rel
    texts = {rel: (S / rel).read_text() for rel in sources}
    imports = {rel: [d.replace('.', '/') + '.lean' for d in re.findall(r'^import (\S+)', t, re.M)
                     if d.startswith('NLA.')] for rel, t in texts.items()}
    closures = {}
    def closure(rel):
        if rel not in closures:
            closures[rel] = {rel}
            for dep in imports[rel]:
                closures[rel] |= closure(dep)
        return closures[rel]
    assert closure('Solution.lean') == set(sources)
    for rel, text in texts.items():
        code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code), rel
        assert 'Challenge' not in ' '.join(re.findall(r'^import (\S+)', text, re.M)), rel
    results = []
    for name in cfg['theorem_names']:
        short = name.removeprefix('NLA.MI13.')
        pattern = re.compile(r'^(?:theorem|lemma) ' + re.escape(short) + r'\b.*?:= by', re.M | re.S)
        matches = [(rel, m) for rel, t in texts.items() for m in pattern.finditer(t)]
        assert len(matches) == 1, name
        rel, match = matches[0]
        frozen = pattern.search((S / 'Challenge.lean').read_text())
        assert frozen and match.group(0) == frozen.group(0), name
        results.append({'declaration': name, 'file': rel,
                        'line': texts[rel].count('\n', 0, match.start()) + 1,
                        'file_sha256': sources[rel], 'sorry_count': 0,
                        'axioms': report['observed_axioms'][name],
                        'comparator_config': 'comparator.json',
                        'verification_status': 'Actual source-bound local Lean elaboration and kernel trust assertions passed. Fresh Linux Comparator and isolation checks pending.'})
    assert not P.exists()
    P.mkdir()
    metadata_old = {'README.md', 'formalization.yaml', 'STATE.json', 'WORKSPACE-MANIFEST.json'}
    for f in sorted(S.rglob('*')):
        if not f.is_file():
            continue
        rel = f.relative_to(S).as_posix()
        if rel in metadata_old:
            rel = 'statement-history/frozen-handoff/' + rel
        elif f.suffix == '.lean' and rel not in sources and rel != 'Challenge.lean':
            rel += '.txt'
        if rel == 'lakefile.toml':
            copy(f, 'statement-history/frozen-handoff/lakefile.toml')
        else:
            copy(f, rel)
    oldlake = (S / 'lakefile.toml').read_text()
    assert oldlake.count('defaultTargets = ["Challenge"]') == 1
    assert 'name = "Solution"' not in oldlake
    newlake = oldlake.replace('defaultTargets = ["Challenge"]', 'defaultTargets = ["Solution"]')
    newlake += '\n[[lean_lib]]\nname = "Solution"\n'
    put('lakefile.toml', newlake)
    put('verification/packaging/LAKE-REGISTRATION.patch', ''.join(difflib.unified_diff(
        oldlake.splitlines(True), newlake.splitlines(True), fromfile='frozen/lakefile.toml', tofile='lakefile.toml')))
    copy(B / 'MI13-ROOT-FREEZE-ACCEPTANCE.json', 'statement-audit/COORDINATOR-ACCEPTANCE.json')
    copy(B / 'MI13-LOCAL-COMPLETE-53.json', 'verification/LOCAL-COMPLETE.json')
    bound = set()
    origins = {}
    visited = set()
    def authenticate(path, module):
        path = Path(path).resolve()
        node = (str(path), module)
        if node in visited:
            return
        visited.add(node)
        j = read(path)
        assert j.get('end') and j['platform'] == 'darwin' and j['threads'] == 1 and j['memory_cap_mib'] == 4096
        c = next(c for c in j['commands'] if c['module'] == module)
        rel = module.replace('.', '/') + '.lean'
        assert c['source_sha256'] == sources[rel]
        assert all(j['source_inputs'][d] == sources[d] for d in closure(rel))
        bound.add(path)
        if c.get('status') == 'reused_exact_successful_local_output':
            prior = Path(c['prior_receipt'])
            assert sha(prior) == c['prior_receipt_sha256']
            child = next(x for x in read(prior)['commands'] if x['module'] == module)
            assert child['output_sha256'] == c['output_sha256']
            authenticate(prior, module)
        else:
            assert c.get('exit_code') == 0
            log = path.parent / (module + '.log')
            assert sha(log) == c['log_sha256'] and 'error:' not in log.read_text()
            bound.add(log)
            origins[module] = {'receipt': str(path), 'receipt_sha256': sha(path),
                               'log': str(log), 'log_sha256': sha(log), **c}
    for rel in sources:
        authenticate(report['receipt'], rel[:-5].replace('/', '.'))
    bound |= {L / 'ASSEMBLY-53.json', L / 'serial_compile_v3.py', L / 'LOCAL-ENVIRONMENT.json'}
    pathmap = {}
    for f in sorted(bound):
        assert f.is_relative_to(L)
        rel = 'verification/local-development/' + f.relative_to(L).as_posix()
        copy(f, rel)
        pathmap[str(f)] = {'path': rel, 'sha256': sha(f)}
    dump('verification/local-development/PATH-MAP.json', pathmap)
    dump('verification/local-development/COMMAND-ORIGINS.json', origins)
    dump('ACTIVE-SOURCE-MANIFEST.json', {'source_sha256': sources, 'Solution_closure_files': 22,
                                       'frozen_Challenge_sha256': sha(S / 'Challenge.lean'),
                                       'local_run': 53, 'canonical_Linux_verification': 'pending'})
    dump('IMPLEMENTATION-MAP.json', {'results': results})
    d = yaml.safe_load((S / 'formalization.yaml').read_text())
    d['project']['description'] = 'Full complex rectangular MI-13 inequality with coefficient two, actual Euclidean operator and Frobenius norms and the two largest actual singular values. All ranks, both dimension orderings and every m,n at least two are retained.'
    for x in d['sources']:
        if '/0907.3913' in x['id']:
            x['note'] = 'The refined commutator bound is proved internally in Lean by a finite spectral and SVD argument; the literature theorem is not assumed.'
    for x in d['related_formalizations']:
        if '/mathlib4/' in x['id']:
            x['note'] = 'Pinned actual Euclidean maps, ordered singular values, Gram eigenbases, orthonormal extension, Rayleigh extrema, complex unit-circle lemmas and block algebra are genuinely reused.'
        if '/leancert/' in x['id']:
            x['note'] = 'Actual kernel-mode exact half positivity and normalization certificate; positivity is consumed by the Frobenius averaging proof. All variable inequalities remain symbolic; no interval subdivision.'
    d['automation']['notes'] = 'Exact numerical and mathematical statements preceded implementation, with two independent statement approvals and actual elaboration. Source development and debugging used one serial local Lean process. Final source reviews and non-root Linux Comparator are separate recorded gates; neither a source scan nor an evidence audit is an execution.'
    d['status'] = {'scope': d['project']['description'], 'sorry_count': 0, 'sorry_in_definitions': 0,
                   'axioms': cfg['permitted_axioms'], 'main_results': results,
                   'whole_problem_verified': False,
                   'source_scan_note': 'All implementation sources are hole-free. Challenge has 36 intentional specification placeholders and is never imported by Solution.'}
    d['fidelity']['divergences'] = 'The exact original target is retained. The refined commutator inequality is proved internally. Sum-index padding into m+n replaces the informal max(m,n) padding, with proved preservation of actual norms and every zero-extended singular value.'
    d['review'] = {'status': 'Two final nonauthor proof reports pending coordinator acceptance; exact statements already approved.',
                   'reviewers': [], 'notes': 'Pinned Tau Ceti rubrics are applied by AI agents within their recorded scope. No official Tau Ceti service or human peer review is claimed.'}
    d['verification'] = {'local': 'Actual macOS local53 full Solution passes, with source-bound successful reuse and all 36 standard axiom reports.',
                         'local_evidence': 'verification/LOCAL-COMPLETE.json',
                         'Linux_Comparator': 'pending', 'default_kernel_replay': 'pending',
                         'sandbox_and_rejection_controls': 'pending',
                         'publication': 'Private canonical preparation only; no verified-count change.'}
    d['alignment'].update(active_source_manifest='ACTIVE-SOURCE-MANIFEST.json', implementation_map='IMPLEMENTATION-MAP.json')
    put('formalization.yaml', '# yaml-language-server: $schema=../../../docs/lean/schema/v0.4.schema.json\n' + yaml.safe_dump(d, sort_keys=False, allow_unicode=True, width=100))
    put('README.md', README)
    dump('STATE.json', {'phase': 'Complete local proof; final source approval and Linux verification pending',
                       'local_run': 53, 'contracts': 36, 'LeanCert_executed_locally': True,
                       'Comparator_executed': False, 'published': False, 'count_change': 0})
    dump('verification/packaging/TRANSITION.json', {'mathematical_sources_unchanged': True,
          'frozen13': freeze['frozen_files'], 'only_active_frozen_change': 'Register Solution library and select it as default; original lakefile and exact diff retained.',
          'active_lake_sha256': sha(P / 'lakefile.toml'),
          'historical_Lean_copies': 'Inactive source snapshots carry an additional .txt suffix; original paths and unchanged byte hashes are in RETAINED-PATHS.json.',
          'local_sources_checked': 22, 'local_contracts_checked': 36, 'Linux_Comparator_run': False})
    dump('verification/RETAINED-PATHS.json', retained)
    dump('PACKAGE-MANIFEST.json', {'stage': 'local53 preparation before final reviews and Linux run',
          'files': {str(f.relative_to(P)): sha(f) for f in sorted(P.rglob('*')) if f.is_file()}})
    print(json.dumps({'package': str(P), 'files': len(list(P.rglob('*'))),
                      'active_Lean_sources': len(list(P.rglob('*.lean'))),
                      'actual_command_origins': len(origins), 'reuse_nodes': len(visited)}, indent=2))

README = '''# MI-13 Lean formalization

This formalization proves the original complex rectangular inequality

```
‖ABC − CBA‖F² ≤ 2 ‖B‖op² (σ₁(A)² + σ₂(A)²) ‖C‖F²
```

for every m,n ≥ 2, complex m-by-n A,C and n-by-m B. The norms are the actual Euclidean operator and Frobenius norms; the singular values are Mathlib's actual decreasing singular values. Zero matrices, deficient ranks, repeated values and both dimension orderings are included.

**Local Lean compilation passed; final Linux verification is pending.** The actual serial macOS run and exact successful reuse are recorded in [LOCAL-COMPLETE.json](verification/LOCAL-COMPLETE.json) and the [command origins](verification/local-development/COMMAND-ORIGINS.json). All 36 exported contracts have measured axiom sets containing only propext, Classical.choice and Quot.sound. This is distinct from a fresh non-root Linux default-kernel, Comparator, sandbox and rejection-control run. Final independent proof reviews are being reconciled before publication.

Read the [numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/MI13/Definitions.lean), independent [Challenge](Challenge.lean), [source correspondence](SourceCorrespondence.md) and [Solution](Solution.lean). Challenge contains deliberate specification holes and is never imported by the implementation. All 36 declarations are selected by [comparator.json](comparator.json), with no replaceable definitions. [IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json) gives their exact defining files.

The refined commutator bound is proved internally using the actual Hilbert–Schmidt commutator operator, a maximal eigenvalue, a two-vector eigenspace argument, and cancellation of one SVD coordinate. Every contraction is the average of two unitaries. Actual block padding preserves both norms and all zero-extended singular values, yielding the rectangular theorem. Padding uses m+n rather than the informal proof's max(m,n), with the same coefficient. A genuine 2-by-2 example checks sharpness.

The only LeanCert interval calculation is the exact positive half certificate in kernel mode, consumed in Frobenius averaging. Matrix, spectral and variable scalar arguments are symbolic; there is no interval grid or numerical sampling. Direct pinned Mathlib lemmas are reused for the unit-circle lift.

The [freeze](STATEMENT-FREEZE.json) and historical reports retain their original preparatory wording. Later source code and runtime records do not rewrite that history. All mathematical frozen inputs are unchanged. The sole operational Lake change registers Solution and selects it as the default; the [diff](verification/packaging/LAKE-REGISTRATION.patch) and original file are retained. Inactive historical Lean copies have a .txt suffix and an explicit original-path/hash map.

With pinned dependencies available, run `lake build` in this directory. Final Linux verification uses the repository's shared [harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-13/lean /absolute/path/to/nla-lean-tools
```

Formalization contributor: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance is disclosed. Nobori's original problem, Audenaert's refined commutator theorem, the repository reduction, and Mathlib, LeanCert, Comparator, Schiffer and Forsythe contributions retain their attribution. Scoped AI-agent review is not official Tau Ceti endorsement or human peer review. [License](LICENSE).
'''

if __name__ == '__main__':
    main()

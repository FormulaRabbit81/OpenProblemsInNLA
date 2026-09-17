#!/usr/bin/env python3
"""Prepare only this candidate handoff; static checks, no Lean or Git."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

P = Path('/tmp/nla-lean-next-20260915/next-proofs/MI-13')
L = Path('/private/tmp/nla-lean-local-shared-20260916')
R = Path(__file__).resolve().parent
candidate = P / 'NLA/MI13/CancelledSVD.lean'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
checks = []
bindings = {}


def check(name, ok):
    checks.append({'name': name, 'pass': bool(ok)})
    if not ok:
        raise AssertionError(name)


def write(name, obj):
    path = R / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')


def bind(path, kind, copy=None, detail=None):
    path = Path(path)
    key = str(path)
    digest = sha(path)
    if key in bindings:
        check('stable binding ' + key, digest == bindings[key]['sha256'])
    else:
        bindings[key] = {'source': key, 'sha256': digest, 'bytes': path.stat().st_size,
                         'kind': kind, 'detail': detail}
    if copy:
        target = R / copy
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(path.read_bytes())
        bindings[key].setdefault('packet_copies', []).append(copy)
        check('exact packet copy ' + copy, sha(target) == digest)
    return digest


frozen = read(P / 'STATEMENT-FREEZE.json')['frozen_files']
source_guard = {str(P / name): sha(P / name) for name in frozen}
for name, expected in frozen.items():
    check('frozen input unchanged ' + name, sha(P / name) == expected)
    bind(P / name, 'immutable-frozen-input', 'frozen/' + name)
bind(P / 'STATEMENT-FREEZE.json', 'accepted-statement-freeze', 'frozen/STATEMENT-FREEZE.json')
bind(candidate, 'new-authored-unrun-candidate', 'candidate.lean.txt')
text = candidate.read_text()
code = re.sub(r'/-.*?-/', '', text, flags=re.S)
code = re.sub(r'--[^\n]*', '', code)
check('no holes extra axioms unsafe or native computation', not re.search(
    r'\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac|implemented_by|extern)\b', code))
check('kernel trust and no implicit variables', 'set_option leancert.trust "kernel"' in code and
      'set_option autoImplicit false' in code)
check('no undocumented change or show', not re.search(r'\b(?:change|show)\b', code))
check('required attribution without email',
      'George Stepaniants' in text and 'Department of Computing and Mathematical Sciences' in text and
      'California Institute of Technology' in text and 'Nobori' in text and 'Audenaert' in text and
      not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}', text))
names = ['svd_corner_functional', 'cancelled_svd_bound']
headers = {m.group(1): re.sub(r'\s*:=\s*by$', '', m.group(0)).rstrip()
           for m in re.finditer(r'^theorem (\w+)\b[\s\S]*?\s*:=\s*by\b', text, re.M)}
specs = {row['name'].split('.')[-1]: row for row in read(P / 'STATEMENT-HEADERS.json')['declarations']}
for name in names:
    check('exact frozen header ' + name, headers[name] == specs[name]['header'])
check('exact new contract set', set(headers) & set(specs) == set(names))
check('exact trust assertions', re.findall(r'^#assert_trust kernel (\w+)', code, re.M) == names)
check('exact axiom prints', re.findall(r'^#print axioms (\w+)', code, re.M) == names)
write('HEADERS.json', {'contracts': [specs[name] for name in names],
                      'source_sha256': sha(candidate), 'exact_frozen_headers': True})

modules = {}
def visit(module):
    if module in modules:
        return
    path = P / (module.replace('.', '/') + '.lean')
    source = path.read_text()
    imports = re.findall(r'^import\s+(\S+)', source, re.M)
    check('no Challenge dependency ' + module, not any('Challenge' in x for x in imports))
    modules[module] = {'source': str(path), 'sha256': sha(path), 'imports': imports}
    if module != 'NLA.MI13.CancelledSVD':
        source_guard[str(path)] = sha(path)
        bind(path, 'unchanged-project-dependency', 'dependencies/' + module.replace('.', '/') + '.lean.txt',
             'Source snapshot for this candidate; not a new independent proof review.')
    for dependency in imports:
        if dependency.startswith('NLA.'):
            visit(dependency)
visit('NLA.MI13.CancelledSVD')
check('exact direct project imports', modules['NLA.MI13.CancelledSVD']['imports'] ==
      ['NLA.MI13.ElementaryBounds', 'NLA.MI13.UnitaryInvariance', 'NLA.MI13.CommutatorEigenspaces'])
write('IMPORT-CLOSURE.json', {'scope': 'Project source identities, not compiled output acceptance.',
                            'modules': modules})

mp = L / '.lake/packages/mathlib'
api = {
 'Mathlib/Algebra/Module/LinearMap/Defs.lean': {
    'lines': ['476-508', '1014-1079'],
    'identities': ['LinearMap.comp', 'LinearMap.comp_apply', 'LinearMap.mulLeftRight',
                   'LinearMap.mulLeftRight_apply']},
 'Mathlib/LinearAlgebra/Matrix/Defs.lean': {
    'lines': ['290-309'], 'identities': ['Matrix.add_apply', 'Matrix.smul_apply', 'Matrix.sub_apply']},
 'Mathlib/Data/Matrix/Mul.lean': {
    'lines': ['370-379', '478-487', '515-521'],
    'identities': ['Matrix.diagonal_mul', 'Matrix.mul_diagonal', 'Matrix.mul_assoc',
                   'Matrix.sub_mul', 'Matrix.mul_sub']},
 'Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean': {
    'lines': ['125-143'], 'identities': ['Matrix.conjTranspose_conjTranspose']},
 'Mathlib/Algebra/BigOperators/Ring/Finset.lean': {
    'lines': ['50-66'], 'identities': ['Finset.mul_sum']},
 'Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean': {
    'lines': ['298-308'], 'identities': ['Finset.sum_add_distrib via to_additive prod_mul_distrib']},
 'Mathlib/Algebra/Order/BigOperators/Group/Finset.lean': {
    'lines': ['98-118'], 'identities': ['Finset.sum_le_sum via to_additive prod_le_prod\'']},
 'Mathlib/Data/Fin/Basic.lean': {
    'lines': ['48-77'], 'identities': ['Fin equality by equality of values']},
}
for name, scope in api.items():
    scope['sha256'] = bind(mp / name, 'pinned-primary-api', 'primary/' + name + '.txt', scope)
check('pinned Mathlib checkout', (mp / '.git/HEAD').read_text().strip() ==
      '0df444a360eaa60ab8c11dca51a86af692955474')
bind(mp / '.git/HEAD', 'filesystem-only-checkout-identity', 'primary/mathlib-HEAD.txt')
lock = read(P / 'lake-manifest.json')
check('shared package revisions match frozen pins',
      {p['name']: p['rev'] for p in lock['packages']} ==
      {p['name']: p['rev'] for p in read(L / 'lake-manifest.json')['packages']})
write('PRIMARY-API.json', {'mathlib_revision': '0df444a360eaa60ab8c11dca51a86af692955474',
                        'source_read_only': True, 'sources': api})

receipt = L / 'runs/development-40/RECEIPT.json'
assembly = L / 'ASSEMBLY-40.json'
log = L / 'runs/development-40/NLA.MI13.UnitaryInvariance.log'
d = read(receipt)
command = next(c for c in d['commands'] if c['module'] == 'NLA.MI13.UnitaryInvariance')
for path, copy in [(receipt, 'context/local40/RECEIPT.json'), (assembly, 'context/ASSEMBLY-40.json'),
                   (log, 'context/local40/NLA.MI13.UnitaryInvariance.log')]:
    bind(path, 'prior-UnitaryInvariance-runtime-context', copy,
         'Only the current UnitaryInvariance command/source/log identity checked here; not a new whole-run review.')
check('local40 actual assembly identity', sha(assembly) == d['assembly_sha256'])
check('current UnitaryInvariance matches actual local40 source',
      command['source_sha256'] == sha(P / 'NLA/MI13/UnitaryInvariance.lean') ==
      sha(L / 'NLA/MI13/UnitaryInvariance.lean'))
check('UnitaryInvariance actual local40 exit and log', command['exit_code'] == 0 and
      command['log_sha256'] == sha(log) and 'error:' not in log.read_text())
check('UnitaryInvariance local40 actual resource limits', command['argv'][1:3] ==
      ['--threads=1', '--memory=4096'] and d['max_compiler_processes'] == 1)

after = {path: sha(path) for path in source_guard}
check('frozen and existing dependencies unchanged during handoff', after == source_guard)
for path, row in bindings.items():
    check('final binding ' + path, sha(path) == row['sha256'])
write('SOURCE-GUARD.json', {'scope': 'Frozen files and existing dependencies before/after handoff preparation.',
                          'before': source_guard, 'after': after, 'unchanged': after == source_guard,
                          'only_new_Lean_file_authored': str(candidate)})
write('BINDINGS.json', {'bindings': list(bindings.values())})
write('STATIC-CHECKS.json', {'prepared_utc': datetime.now(timezone.utc).isoformat(),
                          'scope': 'Metadata, source, pin and header checks only; candidate compilation unrun.',
                          'passed': len(checks), 'failed': 0, 'checks': checks})
print(json.dumps({'source_sha256': sha(candidate), 'checks_passed': len(checks),
                  'bindings': len(bindings), 'project_modules_including_candidate': len(modules),
                  'candidate_Lean_execution': 'UNRUN'}))

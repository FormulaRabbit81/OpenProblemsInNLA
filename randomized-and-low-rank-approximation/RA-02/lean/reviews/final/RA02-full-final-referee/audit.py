"""Read-only source/local-evidence audit; does not run Lean, Lake, Git or Comparator."""
from pathlib import Path
import datetime
import hashlib
import json
import re

B = Path('/tmp/nla-lean-next-20260915')
L = Path('/private/tmp/nla-lean-local-shared-20260916')
S = B / 'next-proofs/RA-02'
OUT = B / 'reviews/RA02-full-final-referee'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
bindings, checks = {}, []

def check(label, value):
    checks.append({'check': label, 'pass': bool(value)})
    if not value:
        raise AssertionError(label)

def bind(path, expected=None):
    path = Path(path)
    h = sha(path)
    if expected is not None:
        check('digest ' + str(path), h == expected)
    bindings[str(path)] = h
    return path

def read(path, expected=None):
    return json.loads(bind(path, expected).read_text())

def strip_comments(text):
    # The reviewed sources contain conventional nested Lean block/line comments.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    check('comments balanced', depth == 0)
    return ''.join(out)

assembly = read(L / 'ASSEMBLY-19.json', 'fad8ce15a1e2db0196e7e888e1d6d0530f42594eeda4fb91ab1f3fdd043c8a1a')
acceptance = read(B / 'RA02-LOCAL-DEVELOPMENT-ACCEPTANCE.json', '20065f375d68844883266d7ec86176b07ddcb652710c693dd67e3d2b1ff005f3')
freeze = read(S / 'STATEMENT-FREEZE.json', '1cdb8abadede54667e539995ae1ff1eba8fb4aa5899f0c5c3ee954a1b845d405')
selected = {p: v for p, v in assembly['sources'].items() if p.startswith('NLA/RA02/')}
check('35 selected source files', len(selected) == 35)
source_map, texts, imports = {}, {}, {}
for rel, value in selected.items():
    p = bind(value['source'], value['sha256'])
    bind(L / rel, value['sha256'])
    logical = 'Solution.lean' if rel.endswith('/Complete.lean') else rel
    check('accepted source ' + rel, acceptance['accepted_source_sha256'][logical] == value['sha256'])
    text = p.read_text()
    code = strip_comments(text)
    check('no hole or untrusted extension ' + rel,
          re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac|elab|macro|initialize|implemented_by|extern)\b', code) is None)
    check('no unsafe option ' + rel,
          re.search(r'set_option\s+(?:debug|trace|interpreter|compiler|maxRecDepth|maxHeartbeats)|set_option\s+leancert\.trust\s+"(?!kernel)', code) is None)
    check('explicit implicit-variable policy ' + rel, 'set_option autoImplicit false' in code)
    imported = [d for line in code.splitlines() if line.startswith('import ') for d in line[7:].split()]
    check('trusted import families ' + rel, all(d.startswith(('NLA.RA02.', 'Mathlib.', 'LeanCert.')) for d in imported))
    check('no Challenge import ' + rel, 'Challenge' not in imported)
    mod = rel[:-5].replace('/', '.')
    imports[mod] = [d for d in imported if d.startswith('NLA.')]
    texts[mod] = code
    source_map[rel] = {'path': str(p), 'sha256': value['sha256'], 'lines_read': len(text.splitlines()), 'read_scope': 'complete source read manually'}

check('no foreign local proof imports', all(d in imports for ds in imports.values() for d in ds))
def closure(mod, seen=None):
    seen = set() if seen is None else seen
    check('acyclic import ' + mod, mod not in seen)
    return {mod} | {x for d in imports[mod] for x in closure(d, seen | {mod})}
closures = {mod: closure(mod) for mod in imports}
check('Complete reaches all 35 sources', closures['NLA.RA02.Complete'] == set(imports))

for rel, h in freeze['frozen_files'].items():
    bind(S / rel, h)
check('exact 9-file frozen boundary', len(freeze['frozen_files']) == 9)
check('active Definitions identical to freeze', selected['NLA/RA02/Definitions.lean']['sha256'] == freeze['frozen_files']['NLA/RA02/Definitions.lean'])
challenge = strip_comments((S / 'Challenge.lean').read_text())
config = read(S / 'comparator.json')
names = config['theorem_names']
check('27 unique configured exports', len(names) == len(set(names)) == 27)
check('no definition holes', config['definition_names'] == [])
check('only standard permitted axioms', set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'})
check('Challenge imports only shared Definitions', re.findall(r'^import (.*)$', challenge, re.M) == ['NLA.RA02.Definitions'])
check('27 intentional Challenge holes', len(re.findall(r'\bsorry\b', challenge)) == 27)
declarations = {}
for mod, code in texts.items():
    for m in re.finditer(r'\btheorem\s+(\w+)\s*(.*?)\s*:=\s*by', code, re.S):
        name = 'NLA.RA02.' + m.group(1)
        check('unique theorem ' + name, name not in declarations)
        declarations[name] = (mod, re.sub(r'\s+', '', m.group(2)))
for m in re.finditer(r'\btheorem\s+(\w+)\s*(.*?)\s*:=\s*by', challenge, re.S):
    name = 'NLA.RA02.' + m.group(1)
    check('exact frozen header ' + name, name in declarations and declarations[name][1] == re.sub(r'\s+', '', m.group(2)))
check('all configured theorems defined', set(names) <= set(declarations))
check('single explicit kernel interval proof', sum(code.count('interval_decide') for code in texts.values()) == 1 and 'interval_decide (trust := kernel)' in texts['NLA.RA02.Numerical'])
check('certificate source dependency chain',
      '_ ≤ 3 := exp_one_bound' in texts['NLA.RA02.Numerical']
      and '(rank_denominator_le_three r)' in texts['NLA.RA02.ExponentialComparison']
      and 'exponential_tail_factor r hr' in texts['NLA.RA02.FinalCounterexample'])

rp = L / 'runs/development-19/RECEIPT.json'
terminal = read(rp, acceptance['receipt_sha256'])
check('actual terminal local success', bool(terminal['end']) and terminal['completed_modules'] == 35 and not terminal['failed_modules'] and not terminal['blocked_modules'])
check('actual resource policy', terminal['platform'] == 'darwin' and terminal['threads'] == 1 and terminal['max_compiler_processes'] == 1 and terminal['memory_cap_mib'] == 4096)
check('actual frozen assembly', terminal['assembly_sha256'] == sha(L / 'ASSEMBLY-19.json'))
bind(L / 'serial_compile_v3.py', terminal['runner_sha256'])
environment = read(L / 'LOCAL-ENVIRONMENT.json')
bind(environment['compiler'], terminal['compiler_sha256'])
check('reported local scope remains limited', not acceptance['canonical_verification_completed'] and not acceptance['comparator_run'] and acceptance['count_change'] == 0)

receipt_cache = {str(rp): terminal}
def get_receipt(p):
    key = str(p)
    if key not in receipt_cache:
        receipt_cache[key] = read(p)
    return receipt_cache[key]
def rel_of(mod):
    return mod.replace('.', '/') + '.lean'
def olean(mod):
    return L / '.lake/build/lib/lean' / (mod.replace('.', '/') + '.olean')
origins = {}
chain_lengths = {}
def resolve(mod, c, path, depth=0):
    check('bounded receipt chain ' + mod, depth < 30)
    expected = selected[rel_of(mod)]['sha256']
    check('receipt source binding ' + mod, c.get('source_sha256') == expected)
    bind(olean(mod), c['output_sha256'])
    if c.get('status') == 'reused_exact_successful_local_output':
        if 'prior_command' in c:
            matches = []
            for candidate in (L / 'runs').glob('development-*/RECEIPT.json'):
                j = json.loads(candidate.read_text())
                if j.get('end') and c['prior_command'] in j.get('commands', []):
                    matches.append(candidate)
            check('embedded prior command has actual terminal receipt ' + mod, bool(matches))
            previous = sorted(matches)[0]
            read(previous)
            return resolve(mod, c['prior_command'], previous, depth + 1)
        previous = bind(c['prior_receipt'], c['prior_receipt_sha256'])
        check('reused complete source closure ' + mod,
              c['transitive_source_hashes'] == {rel_of(d): selected[rel_of(d)]['sha256'] for d in closures[mod]})
        j = get_receipt(previous)
        check('prior receipt terminal ' + mod, bool(j.get('end')))
        matches = [v for v in j['commands'] if v.get('module') == mod and v.get('source_sha256') == expected and v.get('output_sha256') == c['output_sha256']]
        check('unique actual reused origin ' + mod, len(matches) == 1)
        return resolve(mod, matches[0], previous, depth + 1)
    j = get_receipt(path)
    check('direct command recorded in terminal receipt ' + mod, c in j['commands'] and bool(j['end']))
    check('direct successful compilation ' + mod, c.get('exit_code') == 0 and bool(c.get('end')) and c.get('start') < c['end'])
    check('exact compiler invocation ' + mod, c['argv'] == [environment['compiler'], '--threads=1', c['argv'][2], '-o', str(olean(mod)), rel_of(mod)] and c['argv'][2] in ['--memory=3072', '--memory=4096'])
    check('same working directory ' + mod, c['cwd'] == str(L))
    check('compiled source input matches ' + mod, j['source_inputs'][rel_of(mod)] == expected)
    log = bind(path.parent / (mod + '.log'), c['log_sha256'])
    logtext = log.read_text()
    check('no observed compiler error ' + mod, not re.search(r'(?m)^.*error(?:\(|:)', logtext))
    check('no sorry/native axioms in log ' + mod, not re.search(r'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler', logtext))
    for dep, h in c.get('dependency_olean_sha256', {}).items():
        check('dependency belongs to direct imports ' + mod + ' ' + dep, dep in imports[mod])
        bind(olean(dep), h)
    if 'dependency_olean_sha256' in c:
        check('all direct local imports output-bound ' + mod, set(c['dependency_olean_sha256']) == set(imports[mod]))
    origins[mod] = {'receipt': str(path), 'receipt_sha256': sha(path), 'log': str(log), 'log_sha256': sha(log), 'source_sha256': expected, 'output_sha256': c['output_sha256'], 'exit_code': 0, 'argv': c['argv']}
    chain_lengths[mod] = depth
    check('root origin independently corroborated ' + mod, origins[mod] == acceptance['actual_commands'][mod])

for mod in imports:
    matches = [c for c in terminal['commands'] if c['module'] == mod]
    check('one terminal command ' + mod, len(matches) == 1)
    check('terminal source binding ' + mod, terminal['source_inputs'][rel_of(mod)] == selected[rel_of(mod)]['sha256'])
    resolve(mod, matches[0], rp)

complete_log = Path(origins['NLA.RA02.Complete']['log']).read_text()
axioms = {name: [s.strip() for s in raw.split(',') if s.strip()] for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", complete_log)}
check('complete 27-export actual axiom report', set(axioms) == set(names))
check('27 exports standard axioms only', all(set(a) <= set(config['permitted_axioms']) for a in axioms.values()))
check('all 27 trust commands present in compiled wrapper', all('#assert_trust kernel ' + name in texts['NLA.RA02.Complete'] for name in names))
check('exact dependency lock pins', {p['name']: p['rev'] for p in read(S / 'lake-manifest.json')['packages']} == acceptance['dependency_commits'])

# Scope/source provenance hashes are rechecked, without making a new remote/Git retrieval claim.
for n in ['REVIEW-PLAN.md','STANDARDS-PROVENANCE.json','SOURCE-PROVENANCE.json']:
    bind(S / n)
for r in read(S / 'SOURCE-PROVENANCE.json')['source_records']:
    bind(S / r['packet_path'], r['packet_sha256'])
for r in read(S / 'STANDARDS-PROVENANCE.json')['records']:
    bind(S / r['packet_path'], r['sha256'])
for p, h in freeze['statement_review_manifest_bindings'].items():
    bind(p, h)
for rel in ['Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/Analysis/Matrix/PosDef.lean',
            'Mathlib/Analysis/Matrix/Spectrum.lean','Mathlib/Analysis/InnerProductSpace/Rayleigh.lean',
            'Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean','Mathlib/Analysis/Complex/Exponential.lean']:
    bind(L / '.lake/packages/mathlib' / rel)

result = {'reviewer': '/root/ra02_full_final_referee', 'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'scope': 'Full nonauthor source review and independent audit of existing local compilation evidence; no new compiler run.',
          'source_files': len(source_map), 'source_lines_read': sum(v['lines_read'] for v in source_map.values()),
          'frozen_contracts': len(names), 'frozen_files': len(freeze['frozen_files']),
          'actual_successful_origins': len(origins), 'fresh_commands_in_development19': sum('status' not in c for c in terminal['commands']),
          'reused_commands_in_development19': sum(c.get('status') == 'reused_exact_successful_local_output' for c in terminal['commands']),
          'observed_axioms': axioms, 'checks': checks, 'bindings': bindings,
          'check_count': len(checks), 'binding_count': len(bindings), 'all_checks_passed': all(c['pass'] for c in checks),
          'canonical_linux_verified': False, 'comparator_run': False, 'new_compiler_run': False, 'count_change': 0}
(OUT / 'SOURCE-MAP.json').write_text(json.dumps(source_map, indent=2) + '\n')
(OUT / 'LOCAL-ORIGINS.json').write_text(json.dumps({'origins': origins, 'reuse_chain_depths': chain_lengths}, indent=2) + '\n')
(OUT / 'CHECKS.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['source_files','source_lines_read','frozen_contracts','actual_successful_origins','fresh_commands_in_development19','reused_commands_in_development19','check_count','binding_count','all_checks_passed']}))

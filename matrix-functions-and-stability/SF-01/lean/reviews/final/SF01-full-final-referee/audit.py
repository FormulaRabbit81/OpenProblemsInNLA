"""Independent source and existing-local-evidence audit; no Lean/Lake/Git/Comparator execution."""
from pathlib import Path
import datetime
import hashlib
import json
import re

B = Path('/tmp/nla-lean-next-20260915')
L = Path('/private/tmp/nla-lean-local-shared-20260916')
P = B / 'SF01-canonical-package-local16'
OUT = B / 'reviews/SF01-full-final-referee'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
bindings, checks = {}, []
def check(label, value):
    checks.append({'check': label, 'pass': bool(value)})
    if not value:
        raise AssertionError(label)
def bind(p, expected=None):
    p = Path(p)
    h = sha(p)
    if expected is not None:
        check('digest ' + str(p), h == expected)
    bindings[str(p)] = h
    return p
def read(p, expected=None):
    return json.loads(bind(p, expected).read_text())
def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1; i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1; i += 2
        elif depth:
            if text[i] == '\n': out.append('\n')
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i); i = len(text) if j < 0 else j
        else:
            out.append(text[i]); i += 1
    check('balanced Lean comments', depth == 0)
    return ''.join(out)
def rel_of(mod):
    return mod.replace('.', '/') + '.lean'
def logical(rel):
    return 'Solution.lean' if rel == 'NLA/SF01/FinalChecks.lean' else rel

a = read(B / 'SF01-LOCAL-DEVELOPMENT-ACCEPTANCE.json', '2d7cb89042e7b3c09ad0683001005728a1d10ce645aaca11be32a2c74a7b75c4')
bind(P / 'verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json', sha(B / 'SF01-LOCAL-DEVELOPMENT-ACCEPTANCE.json'))
manifest = read(P / 'PACKAGE-MANIFEST.json', '8ae21a5d5e23bcc6f30dd9d1749040ecdaa900f3541f467d50c318be74e8db68')
for rel, h in manifest['files'].items():
    bind(P / rel, h)
check('package manifest contains every packaged file except itself',
      set(manifest['files']) == {str(p.relative_to(P)) for p in P.rglob('*') if p.is_file() and p.name != 'PACKAGE-MANIFEST.json'})
active = read(P / 'ACTIVE-SOURCE-MANIFEST.json')
assembly = read(L / 'ASSEMBLY-16.json', 'f2436899865783cbd40f9c3e354c8ad9605e1f45c8e624c4d4e61d602b26af2d')
selected = {r: v for r, v in assembly['sources'].items() if r.startswith(('NLA/SF01/', 'NLA/IV03/'))}
check('37 selected sources', len(selected) == 37)
check('37 accepted hashes unchanged in package', active['source_sha256'] == a['accepted_source_sha256'])
texts, imports, source_map = {}, {}, {}
for rel, v in selected.items():
    outrel = logical(rel)
    bind(P / outrel, v['sha256'])
    bind(L / rel, v['sha256'])
    bind(v['source'], v['sha256'])
    check('source accepted ' + rel, a['accepted_source_sha256'][outrel] == v['sha256'])
    text = (P / outrel).read_text()
    code = strip_comments(text)
    check('no implementation holes or untrusted commands ' + rel,
          re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac|elab|macro|initialize|implemented_by|extern)\b', code) is None)
    check('no unsafe/resource option ' + rel,
          re.search(r'set_option\s+(?:debug|trace|interpreter|compiler|maxRecDepth|maxHeartbeats)|set_option\s+leancert\.trust\s+"(?!kernel)', code) is None)
    check('explicit implicit-variable policy ' + rel, 'set_option autoImplicit false' in code)
    imported = [d for line in code.splitlines() if line.startswith('import ') for d in line[7:].split()]
    check('trusted import families ' + rel, all(d == 'Mathlib' or d.startswith(('NLA.SF01.', 'NLA.IV03.', 'Mathlib.', 'LeanCert.')) for d in imported))
    check('no Challenge import ' + rel, 'Challenge' not in imported)
    mod = rel[:-5].replace('/', '.')
    imports[mod] = [d for d in imported if d.startswith('NLA.')]
    texts[mod] = code
    source_map[outrel] = {'package_path': str(P / outrel), 'development_path': str(L / rel),
                          'selected_origin': v['source'], 'sha256': v['sha256'],
                          'lines_read': len(text.splitlines()), 'manual_read_scope': 'complete source',
                          'role': 'historical check probe' if outrel in a['historical_check_source_sha256'] else 'final transitive source'}
check('local imports resolve inside selected source map', all(d in imports for ds in imports.values() for d in ds))
def closure(mod, seen=None):
    seen = set() if seen is None else seen
    check('acyclic import ' + mod, mod not in seen)
    return {mod} | {x for d in imports[mod] for x in closure(d, seen | {mod})}
closures = {m: closure(m) for m in imports}
final_modules = closures['NLA.SF01.FinalChecks']
historical_modules = set(imports) - final_modules
check('31 final transitive sources', len(final_modules) == 31)
check('6 retained historical probes', len(historical_modules) == 6)
check('final closure exactly matches accepted package',
      {logical(rel_of(m)) for m in final_modules} == set(a['final_transitive_source_sha256']) == set(active['final_transitive_import_closure']))
check('historical probes exactly match accepted package',
      {logical(rel_of(m)) for m in historical_modules} == set(a['historical_check_source_sha256']))

freeze = read(P / 'STATEMENT-FREEZE.json')
check('9 frozen input files', len(freeze['frozen_files']) == 9)
for rel, h in freeze['frozen_files'].items():
    bind(P / 'statement-audit/frozen-35083895041/snapshots' / rel, h)
    if rel != 'lakefile.toml': bind(P / rel, h)
frozen_lake = (P / 'statement-audit/frozen-35083895041/snapshots/lakefile.toml').read_text()
check('only Lake default target changes', (P / 'lakefile.toml').read_text() == frozen_lake.replace('defaultTargets = ["Challenge"]', 'defaultTargets = ["Solution"]'))
for p, h in freeze['statement_review_manifest_bindings'].items(): bind(p, h)
config = read(P / 'comparator.json')
names = config['theorem_names']
check('24 distinct Comparator exports', len(names) == len(set(names)) == 24)
check('empty definition hole list', config['definition_names'] == [])
check('only standard allowed axioms', set(config['permitted_axioms']) == {'propext','Classical.choice','Quot.sound'})
challenge = strip_comments((P / 'Challenge.lean').read_text())
check('Challenge imports only shared Definitions', re.findall(r'^import (.*)$', challenge, re.M) == ['NLA.SF01.Definitions'])
check('24 intentional Challenge specification holes', len(re.findall(r'\bsorry\b', challenge)) == 24)
def headers(code):
    return {m.group(1): re.sub(r'\s+', '', m.group(2)) for m in re.finditer(r'\btheorem\s+(\w+)\s*(.*?)\s*:=\s*by', code, re.S)}
declarations = {}
for mod, code in texts.items():
    if mod.startswith('NLA.SF01.'):
        for n, h in headers(code).items():
            check('unique SF theorem ' + n, n not in declarations)
            declarations[n] = (mod, h)
for n, h in headers(challenge).items():
    check('exact frozen statement header ' + n, n in declarations and declarations[n][1] == h)
check('all 24 exact Challenge names configured', set(names) == {'NLA.SF01.' + n for n in headers(challenge)})
check('single explicit kernel LeanCert proof', sum(t.count('interval_decide') for t in texts.values()) == 1 and 'interval_decide (trust := kernel)' in texts['NLA.SF01.Numerical'])
check('LeanCert certificate consumed in initial and all coefficient halving',
      'mul_pos ha half_positive_certificate' in texts['NLA.SF01.Numerical'] and
      'half_positive_certificate, half_positive_certificate' in texts['NLA.SF01.Numerical'] and
      'half_coefficient_positive d.a hd.1' in texts['NLA.SF01.NewtonData'] and
      'half_coefficient_positive d.b hd.2.1' in texts['NLA.SF01.NewtonData'] and
      'initialData, initial_data_valid' in texts['NLA.SF01.NewtonConclusion'])

rp = L / 'runs/development-16/RECEIPT.json'
terminal = read(rp, a['receipt_sha256'])
check('terminal receipt complete', bool(terminal['end']))
check('actual local resource policy', terminal['platform'] == 'darwin' and terminal['threads'] == 1 and terminal['max_compiler_processes'] == 1 and terminal['memory_cap_mib'] == 4096)
check('exact terminal assembly digest', terminal['assembly_sha256'] == sha(L / 'ASSEMBLY-16.json'))
bind(L / 'serial_compile_v3.py', terminal['runner_sha256'])
environment = read(L / 'LOCAL-ENVIRONMENT.json')
bind(environment['compiler'], terminal['compiler_sha256'])
check('reported scope remains local only', not a['canonical_verification_completed'] and not a['comparator_run'] and a['count_change'] == 0)
receipt_cache = {str(rp): terminal}
def get_receipt(p):
    key = str(p)
    if key not in receipt_cache: receipt_cache[key] = read(p)
    return receipt_cache[key]
def olean(mod):
    return L / '.lake/build/lib/lean' / (mod.replace('.', '/') + '.olean')
origins, chain_lengths = {}, {}
def resolve(mod, c, path, depth=0):
    check('bounded receipt origin chain ' + mod, depth < 30)
    expected = selected[rel_of(mod)]['sha256']
    check('receipt source hash ' + mod, c.get('source_sha256') == expected)
    bind(olean(mod), c['output_sha256'])
    if c.get('status') == 'reused_exact_successful_local_output':
        if 'prior_command' in c:
            matches = []
            for candidate in (L / 'runs').glob('development-*/RECEIPT.json'):
                j = json.loads(candidate.read_text())
                if j.get('end') and c['prior_command'] in j.get('commands', []): matches.append(candidate)
            check('embedded prior command belongs to completed receipt ' + mod, bool(matches))
            previous = sorted(matches)[0]; read(previous)
            return resolve(mod, c['prior_command'], previous, depth+1)
        previous = bind(c['prior_receipt'], c['prior_receipt_sha256'])
        check('complete transitive source map for reused module ' + mod,
              c['transitive_source_hashes'] == {rel_of(d): selected[rel_of(d)]['sha256'] for d in closures[mod]})
        j = get_receipt(previous)
        check('prior receipt terminal ' + mod, bool(j.get('end')))
        matches = [v for v in j['commands'] if v.get('module') == mod and v.get('source_sha256') == expected and v.get('output_sha256') == c['output_sha256']]
        check('unique actual reused command ' + mod, len(matches) == 1)
        return resolve(mod, matches[0], previous, depth+1)
    j = get_receipt(path)
    check('direct command recorded in completed receipt ' + mod, c in j['commands'] and bool(j['end']))
    check('actual successful origin command ' + mod, c.get('exit_code') == 0 and bool(c.get('end')) and c['start'] < c['end'])
    check('actual compiler command ' + mod,
          c['argv'] == [environment['compiler'], '--threads=1', c['argv'][2], '-o', str(olean(mod)), rel_of(mod)] and c['argv'][2] in ['--memory=3072','--memory=4096'])
    check('actual compiler cwd ' + mod, c['cwd'] == str(L))
    check('origin source input ' + mod, j['source_inputs'][rel_of(mod)] == expected)
    # Every transitive source present at the direct origin must equal the final reviewed source.
    check('origin entire local source closure matches ' + mod,
          all(j['source_inputs'][rel_of(d)] == selected[rel_of(d)]['sha256'] for d in closures[mod]))
    log = bind(path.parent / (mod+'.log'), c['log_sha256'])
    logtext = log.read_text()
    check('no compiler errors ' + mod, not re.search(r'(?m)^.*error(?:\(|:)', logtext))
    check('no admitted or native axiom in actual log ' + mod, not re.search(r'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler', logtext))
    for dep, h in c.get('dependency_olean_sha256', {}).items():
        check('dependency in direct imports ' + mod + ' ' + dep, dep in imports[mod]); bind(olean(dep), h)
    if 'dependency_olean_sha256' in c:
        check('all direct local dependency outputs bound ' + mod, set(c['dependency_olean_sha256']) == set(imports[mod]))
    origin = {'receipt': str(path), 'receipt_sha256': sha(path), 'log': str(log), 'log_sha256': sha(log),
              'source_sha256': expected, 'output_sha256': c['output_sha256'], 'exit_code': 0, 'argv': c['argv']}
    check('acceptance origin independently corroborated ' + mod, all(a['actual_commands'][mod][k] == v for k,v in origin.items()))
    origins[mod] = origin; chain_lengths[mod] = depth
for mod in sorted(final_modules):
    matches = [c for c in terminal['commands'] if c['module'] == mod]
    check('one final terminal command ' + mod, len(matches) == 1)
    check('terminal source input binding ' + mod, terminal['source_inputs'][rel_of(mod)] == selected[rel_of(mod)]['sha256'])
    resolve(mod, matches[0], rp)
for mod in sorted(historical_modules):
    prior = Path(a['actual_commands'][mod]['receipt']); j = get_receipt(prior)
    matches = [c for c in j['commands'] if c['module'] == mod and c.get('source_sha256') == selected[rel_of(mod)]['sha256'] and c.get('exit_code') == 0]
    check('historical check has actual successful origin ' + mod, len(matches) == 1)
    resolve(mod, matches[0], prior)
final_log = Path(origins['NLA.SF01.FinalChecks']['log']).read_text()
axioms = {name: [s.strip() for s in raw.split(',') if s.strip()] for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", final_log)}
check('exact 24-export actual axiom output', set(axioms) == set(names))
check('all final exports only standard axioms', all(set(xs) <= set(config['permitted_axioms']) for xs in axioms.values()))
check('every export has compiled kernel assertion in its namespace',
      'namespace NLA.SF01' in texts['NLA.SF01.FinalChecks'] and
      set(re.findall(r'^#assert_trust kernel (\w+)$', texts['NLA.SF01.FinalChecks'], re.M)) ==
      {name.removeprefix('NLA.SF01.') for name in names})
check('exact dependency lock pins', {x['name']:x['rev'] for x in read(P / 'lake-manifest.json')['packages']} == a['dependency_commits'])
# Independent package-copy check for every retained original local receipt/log/driver.
pathmap = read(P / 'verification/local-development/PATH-MAP.json')
for original, v in pathmap.items():
    bind(original, v['sha256']); bind(P / v['path'], v['sha256'])

prov = read(P / 'SOURCE-PROVENANCE.json')
for rec in prov['canonical'] + prov['standards'] + prov['structure_examples']:
    bind(rec['private_retained_path'], rec['sha256'])
# These primary API excerpts were inspected directly in the pinned active mathlib.
api_files = ['Analysis/Matrix/Spectrum.lean','Analysis/Matrix/PosDef.lean',
 'LinearAlgebra/Eigenspace/Basic.lean','LinearAlgebra/Eigenspace/Minpoly.lean',
 'LinearAlgebra/Matrix/Gershgorin.lean',
 'LinearAlgebra/Matrix/NonsingularInverse.lean','LinearAlgebra/Matrix/Reindex.lean',
 'LinearAlgebra/Matrix/Kronecker.lean','Data/Matrix/Block.lean',
 'Topology/Instances/Matrix.lean','FieldTheory/IsAlgClosed/Spectrum.lean']
for rel in api_files:
    bind(L / '.lake/packages/mathlib/Mathlib' / rel)
for rel in ['NLA/IV03/Definitions.lean','NLA/IV03/Proof.lean']:
    bind(B / 'IV03-canonical-package' / rel, active['source_sha256'][rel])
    check('Sidney Holden code credit retained ' + rel, 'Sidney Holden' in (P / rel).read_text())
# Audit the literal YAML metadata/result bindings. The retained schema-validation
# log is hashed, not represented as a new independent schema-validator run.
formal_text = (P / 'formalization.yaml').read_text()
bind(P / 'verification/packaging/v0.4.schema.json', '25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce')
bind(P / 'verification/packaging/schema-validation.log')
check('metadata explicitly declines completed canonical verification',
      '  whole_problem_verified: false' in formal_text)
entries = re.findall(r'  - declaration: (\S+)\n    file: (\S+)\n    line: (\d+)\n    file_sha256: (\w+)', formal_text)
check('literal metadata contains exactly 24 theorem bindings', len(entries) == 24 and {e[0] for e in entries} == set(names))
for name, rel, linenum, h in entries:
    bind(P / rel, h)
    check('metadata theorem declaration line ' + name,
          (P / rel).read_text().splitlines()[int(linenum)-1].startswith('theorem ' + name.split('.')[-1]))
check('no contact address in proof or reportable metadata', not any(re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', (P / rel).read_text()) for rel in list(source_map) + ['formalization.yaml','README.md','Challenge.lean']))
result = {'reviewer':'/root/ra02_full_final_referee', 'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope':'Full completely nonauthor mathematical/source review; independent audit of existing local evidence. No new compiler run.',
 'selected_source_files':len(selected), 'final_transitive_source_files':len(final_modules),
 'historical_check_probes':len(historical_modules),
 'source_lines_read':sum(x['lines_read'] for x in source_map.values()),
 'final_transitive_lines_read':sum(x['lines_read'] for x in source_map.values() if x['role']=='final transitive source'),
 'frozen_contracts':len(names), 'frozen_files':len(freeze['frozen_files']),
 'actual_successful_origins':len(origins),
 'fresh_SF_final_commands_in_development16':sum('status' not in c for c in terminal['commands'] if c['module'] in final_modules),
 'reused_SF_final_commands_in_development16':sum(c.get('status')=='reused_exact_successful_local_output' for c in terminal['commands'] if c['module'] in final_modules),
 'terminal_unrelated_failed_modules':terminal['failed_modules'],
 'terminal_unrelated_blocked_modules':terminal['blocked_modules'],
 'observed_final_axioms':axioms, 'checks':checks, 'bindings':bindings,
 'check_count':len(checks),'binding_count':len(bindings),'all_checks_passed':all(x['pass'] for x in checks),
 'new_Lean_or_Lake_run':False,'new_Git_or_cache_action':False,'canonical_Linux_verified':False,
 'Comparator_run':False,'count_change':0}
(OUT / 'SOURCE-MAP.json').write_text(json.dumps(source_map,indent=2)+'\n')
(OUT / 'LOCAL-ORIGINS.json').write_text(json.dumps({'origins':origins,'reuse_chain_depths':chain_lengths},indent=2)+'\n')
(OUT / 'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['selected_source_files','final_transitive_source_files','historical_check_probes','source_lines_read','final_transitive_lines_read','frozen_contracts','actual_successful_origins','fresh_SF_final_commands_in_development16','reused_SF_final_commands_in_development16','check_count','binding_count','all_checks_passed']}))

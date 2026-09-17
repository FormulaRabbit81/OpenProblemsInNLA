"""Read-only source/runtime audit; writes only this new private review packet.

This script invokes Git read operations and hashes existing files. It never runs
Lean, Lake, cache commands, a verifier, or a compiler. Mathematical assessment
and complete source/log reading are recorded separately in REVIEW.md.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

B = Path('/tmp/nla-lean-next-20260915')
L = Path('/private/tmp/nla-lean-local-shared-20260916')
W = B / 'next-proofs/RA-02'
O = Path(__file__).parent
bindings, cache = {}, {}

def sha(p):
    p = Path(p)
    if str(p) not in cache:
        h = hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda: f.read(1024 * 1024), b''):
                h.update(b)
        cache[str(p)] = h.hexdigest()
    bindings[str(p)] = cache[str(p)]
    return cache[str(p)]

def read(p):
    sha(p)
    return Path(p).read_text()

def js(p):
    return json.loads(read(p))

acceptance_path = B / 'RA02-LOCAL-DEVELOPMENT-ACCEPTANCE.json'
assert sha(acceptance_path) == '20065f375d68844883266d7ec86176b07ddcb652710c693dd67e3d2b1ff005f3'
a = js(acceptance_path)
receipt_path = Path(a['receipt'])
r = js(receipt_path)
assembly_path = L / 'ASSEMBLY-19.json'
assembly = js(assembly_path)
env = js(L / 'LOCAL-ENVIRONMENT.json')
assert sha(receipt_path) == a['receipt_sha256']
assert sha(assembly_path) == a['assembly_sha256'] == r['assembly_sha256']
assert sha(L / 'serial_compile_v3.py') == r['runner_sha256']
assert sha(env['compiler']) == r['compiler_sha256'] == a['compiler_sha256']
assert r['end'] and r['platform'] == 'darwin'
assert r['max_compiler_processes'] == r['threads'] == 1
assert r['memory_cap_mib'] == 4096
assert r['failed_modules'] == r['blocked_modules'] == []
assert r['completed_modules'] == 35
assert r['source_inputs'] == {p: v['sha256'] for p, v in assembly['sources'].items()}

sources = {p: v for p, v in assembly['sources'].items() if p.startswith('NLA/RA02/')}
assert len(sources) == 35
canonical = {('Solution.lean' if p.endswith('/Complete.lean') else p): v['sha256']
             for p, v in sources.items()}
assert canonical == a['accepted_source_sha256']
texts, mods, selected = {}, {}, {}
for p, v in sources.items():
    assert sha(L / p) == sha(v['source']) == v['sha256'] == r['source_inputs'][p]
    cp = 'Solution.lean' if p.endswith('/Complete.lean') else p
    assert sha(a['selected_source_locations'][cp]) == v['sha256']
    texts[p] = read(v['source'])
    mods[p[:-5].replace('/', '.')] = p
    selected[cp] = {'source': a['selected_source_locations'][cp], 'sha256': v['sha256'],
                    'lines': len(texts[p].splitlines())}

imports = {m: [x for line in texts[p].splitlines() if line.startswith('import ')
                for x in line[7:].split() if x.startswith('NLA.')]
           for m, p in mods.items()}
closures = {}

def closure(m, seen=()):
    assert m in mods and m not in seen
    if m not in closures:
        closures[m] = {m} | set().union(*(closure(d, seen + (m,)) for d in imports[m]))
    return closures[m]

assert closure('NLA.RA02.Complete') == set(mods)
assert all('import Challenge' not in t for t in texts.values())
outputs = {m: sha(L / '.lake/build/lib/lean' / (p[:-5] + '.olean')) for m, p in mods.items()}
receipts = {}

def receipt(p):
    p = str(Path(p))
    if p not in receipts:
        receipts[p] = js(p)
    return receipts[p]

origins, ancestry, actual_assemblies = {}, {}, {}

def verify(c, path, m, seen=()):
    key = (str(path), m)
    assert key not in seen
    assert c['source_sha256'] == sources[mods[m]]['sha256']
    assert c['output_sha256'] == outputs[m]
    if c.get('status') == 'reused_exact_successful_local_output':
        if 'prior_command' in c:
            candidates = []
            for p in sorted((L / 'runs').glob('development-*/RECEIPT.json')):
                j = receipt(p)
                if j.get('end'):
                    candidates += [(p, v) for v in j['commands'] if v == c['prior_command']]
            assert candidates, (m, 'embedded prior command not independently located')
            prior_path, prior_c = candidates[0]
        else:
            prior_path = Path(c['prior_receipt'])
            assert sha(prior_path) == c['prior_receipt_sha256']
            j = receipt(prior_path)
            assert j.get('end')
            assert c['transitive_source_hashes'] == {
                mods[d]: sources[mods[d]]['sha256'] for d in closure(m)}
            for d in closure(m):
                v = j['source_inputs'][mods[d]]
                assert (v['sha256'] if isinstance(v, dict) else v) == sources[mods[d]]['sha256']
            matches = [v for v in j['commands'] if v.get('module') == m
                       and v.get('source_sha256') == c['source_sha256']
                       and v.get('output_sha256') == c['output_sha256']]
            assert len(matches) == 1
            prior_c = matches[0]
        ancestry.setdefault(m, []).append({'receipt': str(path), 'sha256': sha(path),
            'prior': str(prior_path), 'prior_sha256': sha(prior_path)})
        return verify(prior_c, prior_path, m, seen + (key,))
    assert c['exit_code'] == 0 and c['end'] and c['argv'][0] == env['compiler']
    assert c['cwd'] == str(L) and c['argv'][-1] == mods[m]
    assert c['argv'][1:3] in [['--threads=1', '--memory=4096'], ['--threads=1', '--memory=3072']]
    j = receipt(path)
    assert j['end'] and j['platform'] == 'darwin' and j['max_compiler_processes'] == j['threads'] == 1
    assert j['compiler_sha256'] == r['compiler_sha256']
    local_assembly = L / ('ASSEMBLY-' + path.parent.name.split('-')[-1] + '.json')
    aj = js(local_assembly)
    assert sha(local_assembly) == j['assembly_sha256']
    actual_assemblies[str(local_assembly)] = sha(local_assembly)
    for d in closure(m):
        v = j['source_inputs'][mods[d]]
        assert (v['sha256'] if isinstance(v, dict) else v) == sources[mods[d]]['sha256']
        assert aj['sources'][mods[d]]['sha256'] == sources[mods[d]]['sha256']
    assert c['dependency_olean_sha256'] == {d: outputs[d] for d in imports[m]}
    log = path.parent / (m + '.log')
    assert sha(log) == c['log_sha256']
    t = read(log)
    assert not re.search(r'(^|\n).*error(?:\(|:)', t)
    assert 'sorryAx' not in t and 'declaration uses `sorry`' not in t
    actual = {'receipt': str(path), 'receipt_sha256': sha(path), 'log': str(log),
        'log_sha256': sha(log), 'exit_code': 0, 'source_sha256': c['source_sha256'],
        'output_sha256': c['output_sha256'], 'argv': c['argv']}
    assert actual == a['actual_commands'][m]
    return actual

commands = {c['module']: c for c in r['commands']}
assert set(commands) == set(mods)
for m, c in commands.items():
    origins[m] = verify(c, receipt_path, m)
fresh = [m for m, c in commands.items() if c.get('exit_code') == 0]
reused = [m for m, c in commands.items() if c.get('status') == 'reused_exact_successful_local_output']
assert len(fresh) == 3 and len(reused) == 32

freeze = js(W / 'STATEMENT-FREEZE.json')
frozen = freeze['frozen_files']
assert frozen == a['frozen_files_sha256'] and len(frozen) == 9
for p, h in frozen.items():
    assert sha(W / p) == h
for p, h in freeze['statement_review_manifest_bindings'].items():
    assert sha(p) == h
config = js(W / 'comparator.json')
names = config['theorem_names']
assert len(names) == 27 and config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
complete = texts['NLA/RA02/Complete.lean']
assert re.findall(r'^#print axioms (\S+)', complete, re.M) == names
assert re.findall(r'^#assert_trust kernel (\S+)', complete, re.M) == names
complete_log = read(origins['NLA.RA02.Complete']['log'])
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", complete_log)
assert [n for n, _ in reports] == names
assert all(set(v.split(', ')) == set(config['permitted_axioms']) for _, v in reports)
observed = {n: v.split(', ') for n, v in reports}
assert observed == a['observed_axioms']
challenge = read(W / 'Challenge.lean')
headers = {}
for fq in names:
    name = fq.rsplit('.', 1)[1]
    pat = r'(?m)^theorem ' + re.escape(name) + r'\b(.*?):= by'
    expected = re.search(pat, challenge, re.S).group(1)
    found = [(p, h.group(1)) for p, t in texts.items() for h in [re.search(pat, t, re.S)] if h]
    assert len(found) == 1
    p, actual = found[0]
    assert re.sub(r'\s+', '', expected) == re.sub(r'\s+', '', actual), name
    headers[name] = {'path': p, 'Challenge': expected.strip(), 'implementation': actual.strip(),
                     'normalization': 'whitespace only'}
assert len(re.findall(r'\bsorry\b', re.sub(r'/\-[\s\S]*?\-/','',challenge))) == 27
options = {}
for p, t in texts.items():
    code = re.sub(r'/\-[\s\S]*?\-/','',t)
    code = re.sub(r'--[^\n]*','',code)
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide|unsafe)\b',code), p
    assert not re.search(r'^\s*(?:variable|axiom)\b',code,re.M), p
    os = re.findall(r'^set_option (.*)$', code, re.M)
    assert all(o in ['autoImplicit false', 'leancert.trust "kernel"'] for o in os), (p,os)
    options[p] = os
assert 'interval_decide (trust := kernel)' in texts['NLA/RA02/Numerical.lean']
assert '_ ≤ 3 := exp_one_bound' in texts['NLA/RA02/Numerical.lean']
assert '(rank_denominator_le_three r)' in texts['NLA/RA02/ExponentialComparison.lean']
assert 'exponential_tail_factor r hr hA.isHermitian' in texts['NLA/RA02/FinalCounterexample.lean']

pins = {v['name']: v['rev'] for v in js(W / 'lake-manifest.json')['packages']}
assert pins == a['dependency_commits'] and len(pins) == 10
for dep, h in pins.items():
    p = L / '.lake/packages' / dep
    assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'], text=True).strip() == h
    assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'], text=True)
repo = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
prov = js(W / 'SOURCE-PROVENANCE.json')
for s in prov['source_records']:
    assert sha(W / s['packet_path']) == s['packet_sha256']
    assert sha(s['raw_private_path']) == s['raw_sha256']
    data = subprocess.check_output(['git','-C',str(repo),'show',s['commit']+':'+s['path']])
    assert hashlib.sha256(data).hexdigest() == s['raw_sha256']
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert blob == s['raw_git_blob']

apiroot = L / '.lake/packages/mathlib'
api_files = ['Mathlib/Analysis/Matrix/Spectrum.lean', 'Mathlib/Analysis/Matrix/PosDef.lean',
    'Mathlib/LinearAlgebra/Matrix/PosDef.lean', 'Mathlib/Analysis/InnerProductSpace/Rayleigh.lean',
    'Mathlib/Analysis/InnerProductSpace/Spectrum.lean',
    'Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean',
    'Mathlib/Analysis/Complex/Exponential.lean', 'Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean']
for rel in api_files:
    data = subprocess.check_output(['git','-C',str(apiroot),'show',pins['mathlib']+':'+rel])
    assert hashlib.sha256(data).hexdigest() == sha(apiroot / rel)
for record in js(W / 'STANDARDS-PROVENANCE.json')['records']:
    assert sha(W / record['packet_path']) == record['sha256']
for rel in ['REVIEW-PLAN.md','REUSE-AND-API.md','REUSE-AUDIT.json','PRIMARY-API.json','SEMANTIC-API-PROVENANCE.json']:
    sha(W / rel)
for d in sorted((B / 'reviews').glob('RA02-ie13*')):
    if d == O:
        continue
    for rel in ['MANIFEST.json','REVIEW.md']:
        if (d / rel).exists():
            sha(d / rel)
repair = B / 'local-routine-repairs/development18'
for p in sorted(repair.rglob('*')):
    if p.is_file():
        sha(p)
before = read(repair / 'before/NLA/RA02/ExponentialComparison.lean.txt')
after = read(repair / 'after/NLA/RA02/ExponentialComparison.lean.txt')
assert before.replace('Real.isLittleO_rpow_exp_pos_mul_atTop','isLittleO_rpow_exp_pos_mul_atTop') == after
assert after == texts['NLA/RA02/ExponentialComparison.lean']

checks = {
    'reviewer': '/root/ie13_continuation',
    'role': 'Full independent nonauthor RA-02 proof-source referee and local evidence auditor; earlier nonauthor mathematical/API/statement-continuation reviews, no RA-02 proof implementation',
    'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': 'APPROVED complete source candidate and source-bound local development evidence; canonical Linux verification pending',
    'all35_Lean_files_completely_read': True,
    'total_Lean_lines': sum(len(t.splitlines()) for t in texts.values()),
    'all27_frozen_contracts_and_full_original_manuscript_read': True,
    'full_current_import_closure': list(sorted(mods)),
    'shared_assembly_inputs_matched_to_receipt': len(r['source_inputs']),
    'current_RA02_sources_and_outputs_matched': 35,
    'actual_fresh_local19_modules': fresh,
    'reused_source_bound_modules': reused,
    'all35_origin_logs_completely_read': True,
    'all35_original_executions_exit_zero': True,
    'all_current_dependency_olean_hashes_match_origin_commands': True,
    'all_transitive_local_source_hashes_match_reuse_receipts': True,
    'observed_complete_axioms': observed,
    'frozen_files_unchanged': 9,
    'all27_public_headers': 'Exact after whitespace normalization only',
    'pins': pins,
    'local_run_terminal': r['end'],
    'actual_local19_failures': r['failed_modules'],
    'actual_local19_blocked': r['blocked_modules'],
    'options': options,
    'LeanCert_consumed': 'exp_one_bound -> rank_denominator_le_three -> exponential_tail_factor -> universal_counterexamples -> no_polynomial_trace_factor',
    'numerical_scope': 'One exact exp(1) bound; no interval subdivision, matrix enumeration, numeric eigensolve, rank enumeration, or large rational expansion',
    'final_observed_repair': 'Exactly remove erroneous Real. namespace qualification; actual local18 failure retained and local19 pass inspected',
    'limitations': [
        'No compiler, Lean, Lake or cache command executed by this reviewer; this is an independent audit, not an independent rerun.',
        'Actual executions are macOS serial development builds with pinned shared compiled dependencies.',
        'Development19 runs three modules afresh and reuses 32 exactly source-bound successful outputs; all origin chains are checked.',
        'No fresh Linux build, default-kernel export/replay, Comparator or negative/sandbox controls are supplied by this packet.',
        'No publication commit or upstream PR acceptance, canonical status update or count change.'
    ],
    'count_change': 0
}
(O/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
(O/'SOURCE-BINDINGS.json').write_text(json.dumps(bindings,indent=2,sort_keys=True)+'\n')
(O/'CONTRACT-COMPARISON.json').write_text(json.dumps(headers,indent=2,ensure_ascii=False)+'\n')
(O/'SELECTED-SOURCE-PATHS.json').write_text(json.dumps(selected,indent=2,sort_keys=True)+'\n')
(O/'RUNTIME-ORIGINS.json').write_text(json.dumps({'origins':origins,'reuse_ancestry':ancestry,
    'origin_assemblies':actual_assemblies},indent=2)+'\n')
print(json.dumps({'pass':True,'bindings':len(bindings),'sources':len(texts),
    'lines':checks['total_Lean_lines'],'fresh':len(fresh),'reused':len(reused),'public_contracts':len(headers)}))

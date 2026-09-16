"""Independent read-only audit of retained GitHub execution, not a Lean rerun.

Executor: /root/mf22_publication_referee. Raw evidence was fetched by /root.
The root helper was read for comparison but is not executed by this script.
Only this review directory is written; Git calls only read objects/diffs.
"""
from pathlib import Path
import hashlib
import ast
import json
import re
import subprocess
import zipfile

B = Path('/tmp/nla-lean-next-20260915')
R = B / 'canonical-runs/35081003513'
OUT = Path(__file__).parent
PK = B / 'IE13-canonical-package-v2'
W = '/private/tmp/nla-lean-next-ie13-worktree'
C = '032d4c86c52ffde0c4d440f28527ba43555a0a24'
P = 'linear-systems-and-elimination/IE-13/lean'
TRUSTED = 'ff6abf718126ceb23f933cf4f627f95104461fe8'
checks = []
bindings = {}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def bind(p):
    p = Path(p)
    data = p.read_bytes()
    bindings[str(p)] = sha(data)
    return data

def check(label, value):
    checks.append({'check': label, 'pass': bool(value)})
    if not value:
        raise AssertionError(label)

def git(*args):
    return subprocess.check_output(['git', '-c', 'gc.auto=0', '-C', W, *args])

def load(p):
    return json.loads(bind(p))

meta = load(R / 'run.json')
jobs = load(R / 'jobs.json')['jobs']
arts = load(R / 'artifacts.json')['artifacts']
fetch = load(R / 'FETCH-IDENTITY.json')
check('actual terminal push run on literal requested commit',
      meta['id'] == 35081003513 and meta['head_sha'] == C and
      meta['event'] == 'push' and meta['status'] == 'completed' and
      meta['conclusion'] == 'success' and meta['run_attempt'] == 1)
check('actual workflow is canonical verification',
      meta['path'] == '.github/workflows/lean-verification.yml')
verify = [j for j in jobs if j['id'] == 104744813757][0]
check('verify job succeeded with every actual step successful',
      verify['name'] == 'verify (IE-13, ' + P + ')' and
      verify['conclusion'] == 'success' and
      all(s['conclusion'] == 'success' for s in verify['steps']))
select = [j for j in jobs if j['name'] == 'select'][0]
check('selection job and all steps succeeded', select['conclusion'] == 'success' and
      all(s['conclusion'] == 'success' for s in select['steps']))
control_job = [j for j in jobs if j['name'] == 'checker-controls'][0]
check('separate unchanged-harness controls job honestly skipped',
      control_job['conclusion'] == 'skipped' and not control_job['steps'])
check('only one project verification job',
      len([j for j in jobs if j['name'].startswith('verify (')]) == 1)

E = R / 'artifacts/lean-IE-13/verify-20260916T094450Z-4160'
receipt = load(E / 'result.json')
check('receipt identifies exact actual project, commit and acceptance',
      receipt['repository_commit'] == C and receipt['project'] == P and
      receipt['result'] == 'comparator-accepted' and
      receipt['semantic_review'] == 'not-performed-by-this-command')
entries = {}
for row in git('ls-tree', '-rz', C, '--', P).split(b'\0'):
    if not row:
        continue
    info, name = row.split(b'\t')
    mode, kind, oid = info.decode().split()
    rel = name.decode()[len(P)+1:]
    check('regular committed project blob: ' + rel, kind == 'blob' and mode in ['100644', '100755'])
    entries[rel] = oid
check('exactly all 95 tracked project inputs in receipt',
      set(entries) == set(receipt['input_sha256']) and len(entries) == 95)
data = {}
cat = subprocess.Popen(['git', '-c', 'gc.auto=0', '-C', W, 'cat-file', '--batch'],
                       stdin=subprocess.PIPE, stdout=subprocess.PIPE)
for name, oid in sorted(entries.items()):
    cat.stdin.write((oid + '\n').encode())
    cat.stdin.flush()
    got_oid, kind, size = cat.stdout.readline().decode().split()
    raw = cat.stdout.read(int(size))
    terminator = cat.stdout.read(1)
    check('actual Git blob equals receipt and reviewed package: ' + name,
          got_oid == oid and kind == 'blob' and terminator == b'\n' and
          sha(raw) == receipt['input_sha256'][name] and raw == bind(PK/name))
    data[name] = raw
cat.stdin.close()
cat.wait()
check('batch Git object reader completed', cat.returncode == 0)
package = json.loads(data['PACKAGE-MANIFEST.json'])
check('package manifest closure plus its own file equals exact inputs',
      set(package['files']) | {'PACKAGE-MANIFEST.json'} == set(data))
for name, h in package['files'].items():
    check('package sealed digest: ' + name, sha(data[name]) == h)
source = json.loads(data['ACTIVE-SOURCE-MANIFEST.json'])['source_sha256']
old_map = load(B/'elimination/IE-13/proof-handoffs/repair-35071348416/SOURCE-MAP.json')
check('all 27 active mathematical sources equal own prior full-reviewed closure',
      len(source) == 27 and source == {x['author_path']: x['sha256'] for x in old_map} and
      all(sha(data[n]) == h for n,h in source.items()))
freeze = json.loads(data['STATEMENT-FREEZE.json'])
frozen = freeze['frozen_files_sha256']
check('ten frozen historical boundary inputs retained', len(frozen) == 10)
for name,h in frozen.items():
    check('exact frozen snapshot retained: ' + name,
          sha(data['statement-audit/snapshots/'+name]) == h)
    if name != 'lakefile.toml':
        check('active frozen boundary remains exact: ' + name, sha(data[name]) == h)
check('only accepted Lake default target changes in frozen boundary',
      data['lakefile.toml'] == data['statement-audit/snapshots/lakefile.toml'].replace(
          b'defaultTargets = ["Challenge"]', b'defaultTargets = ["Solution"]'))
config = json.loads(data['comparator.json'])
check('exact configuration receipt with all 28 targets and standard axiom allowlist',
      config == receipt['config'] and len(config['theorem_names']) == 28 and
      len(set(config['theorem_names'])) == 28 and config['definition_names'] == [] and
      config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound'])
names = config['theorem_names']
for protected in ['tools/lean', '.github/workflows/lean-verification.yml']:
    check('trusted shared harness unchanged: ' + protected,
          git('diff', TRUSTED, C, '--', protected) == b'')
lock_bytes = git('show', C + ':tools/lean/source-lock.json')
lock = json.loads(lock_bytes)
tool = receipt['tool_receipt']
check('actual pinned source lock',
      sha(lock_bytes) == receipt['source_lock_sha256'] == tool['source_lock_sha256'] ==
      'b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b')
check('actual Linux Lean and source provenance',
      tool['platform'].startswith('Linux-') and
      tool['forsythe_commit'] == lock['commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62' and
      tool['lean_toolchain'] == lock['lean_toolchain'] == 'leanprover/lean4:v4.33.1' and
      'x86_64-unknown-linux-gnu' in tool['lean_version'] and
      '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in tool['lean_version'])
harness = git('show', C + ':tools/lean/harness.py').decode()
probe_root = Path('/tmp/nla-lean-formalization/linux-infrastructure/source/forsythe')
probe_original = bind(probe_root/'reproduction/checks/sandbox_probe.py')
probe_lock = [x for x in lock['files'] if x['destination']=='reproduction/checks/sandbox_probe.py'][0]
check('original pinned sandbox source exact source-lock hash',sha(probe_original)==probe_lock['sha256'])
fn = [n for n in ast.parse(harness).body if isinstance(n,ast.FunctionDef) and n.name=='ci_probe_source']
check('one explicit pure-text CI probe adapter in committed harness',len(fn)==1)
env = {'Path':Path,'HarnessError':RuntimeError}
exec(compile(ast.Module(body=fn,type_ignores=[]),'<committed ci_probe_source only>','exec'),env)
probe = env['ci_probe_source'](probe_root).encode()
check('actual CI sandbox probe exact committed text adaptation of pinned source',
      sha(probe) == tool['ci_sandbox_probe_sha256'])

logs = {p.name: bind(p).decode() for p in E.glob('*.log')}
comp = logs['comparator.log']
solution_phase = comp[comp.index('Building Solution'):]
for module in ['Challenge', 'Solution']:
    export = [l for l in comp.splitlines() if l.startswith('Exporting #[') and l.endswith(' from '+module)]
    check('actual ordered 28-name export from '+module,
          len(export) == 1 and re.findall(r'\bNLA\.[A-Za-z0-9_.]+',export[0]) == names)
for n in names:
    lists = re.findall(re.escape("'"+n+"' depends on axioms: ")+r'\[([^\]]*)\]', solution_phase)
    check('actual standard transitive axioms for '+n,
          bool(lists) and all(set(s.split(', ')) <= set(config['permitted_axioms']) for s in lists))
for path in source:
    module = path[:-5].replace('/', '.')
    check('actual build log contains complete module '+module,
          bool(re.search(r'Built '+re.escape(module)+r'(?:\s|\()', comp)))
check('actual full replay and Comparator acceptance, not only build',
      comp.index('Building Challenge') < comp.index('Building Solution') <
      comp.index('Running Lean default kernel on solution.') and
      'Lean default kernel accepts the solution' in solution_phase and
      solution_phase.count('Your solution is okay!') == 1 and
      comp.rstrip().endswith('EXIT_STATUS=0'))
check('only exactly 28 deliberate Challenge placeholders; no proof placeholders/errors',
      comp.count('declaration uses `sorry`') == 28 and
      'declaration uses `sorry`' not in solution_phase and
      not any(s in comp for s in ['sorryAx', 'Illegal axiom', 'error:']))
check('actual LeanCert witness half-certificate and witness scale built',
      "'NLA.IE13.half_bounds_certificate' depends on axioms:" in comp and
      "'NLA.IE13.witness_scale' depends on axioms:" in comp and
      'LeanCert' in data['NLA/IE13/WitnessScale.lean'].decode())
for name in ['comparator.log','kernel-controls.log','comparator-controls.log','sandbox.log',
             'dependencies.log','mathlib-cache.log','user-service.log']:
    check('actual successful exit: '+name, logs[name].rstrip().endswith('EXIT_STATUS=0'))
for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
               'RETURN invalid_raw_proof: rejected:',
               'RETURN quotient_postcheck_mismatch: rejected:',
               'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
    check('actual builtin replay control: '+marker, marker in logs['kernel-controls.log'])
for fixture in ['simple_match','simple_mismatch','simple_axiom_issue','simple_kind_mismatch','type_mismatch']:
    check('actual five-case regression: '+fixture,'PASS '+fixture+':' in logs['comparator-controls.log'])
check('all five regressions actually passed', 'PASS: all five Comparator regressions' in logs['comparator-controls.log'])
for name,marker in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),
                    ('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
    check('actual expected rejection: '+name,marker in logs[name] and logs[name].rstrip().endswith('EXIT_STATUS=1'))
uids = re.findall(r'Sandbox UID: (\d+)', logs['sandbox.log'])
check('actual both sandbox modes run as nonroot UID 1001',uids == ['1001','1001'])
for marker in ['MODE build: exit=0','MODE export: exit=0','PASS effective capabilities: none',
               'PASS AF_UNIX socket creation: denied','PASS no_new_privs: set',
               'PASS user namespace: private','PASS pid namespace: private','PASS mnt namespace: private',
               'PASS net namespace: private','PASS ipc namespace: private','PASS uts namespace: private',
               'PASS export .lake write-open: denied',
               'Outer and export fixture contents unchanged; only designated build fixture written.']:
    check('actual sandbox control: '+marker,marker in logs['sandbox.log'])
deps = json.loads(data['lake-manifest.json'])['packages']
for dep in deps:
    check('actual pinned dependency checkout: '+dep['name'],dep['rev'] in logs['dependencies.log'])
check('pinned Mathlib and LeanCert exact revisions',
      {p['name']:p['rev'] for p in deps}['mathlib'] == '0df444a360eaa60ab8c11dca51a86af692955474' and
      {p['name']:p['rev'] for p in deps}['leancert'] == '621a43d7cf21f87872392a01e874f2f1dbddc926')

raw = bind(R/'job-104744813757.log').decode()
select_raw = bind(R/'job-104744724356.log').decode()
check('actual raw runner checkout is literal requested commit, not synthetic merge',
      bool(re.search(r'git log -1 --format=%H\n[^\n]*'+C+r'\n',raw)))
check('raw project validator and final actual verifier completion',
      'python3 tools/lean/validate_manifest.py "$LEAN_PROJECT"' in raw and
      'Manifest schema and comparator coverage: PASS (28 declarations)' in raw and
      'PASS: fresh Comparator run and all controls.' in raw)
raw_plain = '\n'.join(re.sub(r'^\d{4}-[^ ]+ ','',x) for x in raw.splitlines())
line_counts = {}
for p in sorted((R/'artifacts/lean-IE-13').rglob('*.log')):
    content = bind(p).decode()
    lines = [s for s in content.splitlines() if s and not s.startswith('$ ') and not s.startswith('EXIT_STATUS=')]
    check('all nonempty emitted artifact lines occur in actual raw job: '+p.name,
          all(s in raw_plain for s in lines))
    line_counts[p.name] = len(lines)
art = [a for a in arts if a['id'] == 10440806325][0]
archive = bind(R/'lean-IE-13.zip')
check('actual GitHub artifact identity and digest',
      art['name'] == 'lean-IE-13' and art['digest'] == 'sha256:'+sha(archive) and
      sha(archive) == '09d3534e68bdd141eaf64240b58f1bdf58ff1b225b652cb3659efabbb9ba7e73' and
      art['workflow_run']['id'] == meta['id'] and art['workflow_run']['head_sha'] == C and
      not art['expired'])
with zipfile.ZipFile(R/'lean-IE-13.zip') as z:
    members = [n for n in z.namelist() if not n.endswith('/')]
    retained = {str(p.relative_to(R/'artifacts/lean-IE-13')) for p in (R/'artifacts/lean-IE-13').rglob('*') if p.is_file()}
    check('all 13 original ZIP member names exactly retained',set(members)==retained and len(members)==13)
    for name in members:
        check('original authenticated ZIP member bytes: '+name,
              z.read(name)==bind(R/'artifacts/lean-IE-13'/name))

# Bind prior independent full-source and packaging decisions; do not claim that
# this continuation repeats every past mathematical reading from scratch.
for name in ['IE13-mf22-complete','IE13-mf22-final-35067372404',
             'IE13-mf22-repair-35071348416','IE13-mf22-canonical-package-35076646177',
             'IE13-mf22-canonical-package-v2']:
    d = B/'reviews'/name
    for f in ['REVIEW.md','CHECKS.json','MANIFEST.json']:
        bind(d/f)
bind(B/'audit_canonical_runtime.py')
out = {'reviewer':'/root/mf22_publication_referee','actual_executor':'/root/mf22_publication_referee',
       'root_helper_executed':False,'local_lean_execution':False,
       'verdict':'PASS independent runtime continuation of prior complete mathematical and packaging reviews',
       'run':35081003513,'job':104744813757,'commit':C,'literal_head':True,
       'project':P,'all_committed_inputs':95,'unchanged_mathematical_sources':27,
       'exported_and_replayed_contracts':28,'checks':checks,'bindings':bindings,
       'artifact_emitted_line_counts':line_counts,
       'scope':'Independent audit of the same actual GitHub Linux execution. Not another Lean execution, formal proof of checker soundness, publication or count update.'}
(OUT/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
(OUT/'ALL-95-INPUTS.json').write_text(json.dumps({n:{'git_blob':entries[n], 'sha256':sha(data[n])} for n in sorted(data)},indent=2)+'\n')
print(json.dumps({'pass':True,'checks':len(checks),'bindings':len(bindings),'inputs':len(data),
                  'sources':len(source),'exports':len(names),'emitted_lines':sum(line_counts.values())},indent=2))

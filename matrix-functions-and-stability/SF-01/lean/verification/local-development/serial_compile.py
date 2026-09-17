#!/usr/bin/env python3
"""Serial local development compilation; not canonical Comparator acceptance."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
assembly = json.loads((ROOT / 'ASSEMBLY-01.json').read_text())
environment = json.loads((ROOT / 'LOCAL-ENVIRONMENT.json').read_text())
run = ROOT / 'runs' / sys.argv[1]
run.mkdir(parents=True, exist_ok=False)
lock = (ROOT / '.compiler.lock').open('w')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
sources = assembly['sources']
modules = {p[:-5].replace('/', '.'): p for p in sources}
imports = {}
for mod, rel in modules.items():
    assert sha(ROOT / rel) == sources[rel]['sha256'], rel
    imports[mod] = []
    for line in (ROOT / rel).read_text().splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                if dep.startswith('NLA.'):
                    assert dep in modules, (mod, dep)
                    imports[mod].append(dep)
ordered, visiting, visited = [], set(), set()
def visit(mod):
    if mod in visited:
        return
    assert mod not in visiting, ('cycle', mod)
    visiting.add(mod)
    for dep in imports[mod]:
        visit(dep)
    visiting.remove(mod)
    visited.add(mod)
    ordered.append(mod)
for prefix in ['NLA.MI04.', 'NLA.MF07.', 'NLA.SF01.', 'NLA.RA02.', 'NLA.IV03.']:
    for mod in sorted(modules):
        if mod.startswith(prefix):
            visit(mod)
receipt = {
    'scope': 'macOS serial default-kernel development compilation only; no Comparator, sandbox controls or whole-problem acceptance',
    'start': now(), 'assembly_sha256': sha(ROOT / 'ASSEMBLY-01.json'),
    'runner_sha256': sha(__file__), 'environment_sha256': sha(ROOT / 'LOCAL-ENVIRONMENT.json'),
    'compiler_sha256': sha(environment['compiler']), 'platform': sys.platform,
    'max_compiler_processes': 1, 'threads': 1, 'memory_cap_mib': 3072,
    'source_inputs': {p: sources[p]['sha256'] for p in sources},
    'module_order': ordered, 'commands': [], 'count_change': 0,
}
env = os.environ.copy()
env['LEAN_PATH'] = environment['lean_path']
env['LEAN_NUM_THREADS'] = '1'
results = {}
def save():
    (run / 'RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
save()
for mod in ordered:
    rel = modules[mod]
    assert sha(ROOT / rel) == sources[rel]['sha256'], rel
    failed = [dep for dep in imports[mod] if results[dep] != 0]
    if failed:
        results[mod] = 'blocked'
        receipt['commands'].append({'module': mod, 'status': 'not_run', 'failed_dependencies': failed})
        save()
        continue
    output = ROOT / '.lake/build/lib/lean' / (rel[:-5] + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    assert not output.exists(), ('unexpected existing output', output)
    argv = [environment['compiler'], '--threads=1', '--memory=3072', '-o', str(output), rel]
    log = run / (mod + '.log')
    command = {'module': mod, 'argv': argv, 'cwd': str(ROOT), 'start': now(), 'source_sha256': sha(ROOT / rel),
               'dependency_olean_sha256': {dep: sha(ROOT / '.lake/build/lib/lean' / (modules[dep][:-5] + '.olean')) for dep in imports[mod]}}
    print('START', mod, flush=True)
    start = time.monotonic()
    with log.open('w') as stream:
        try:
            child = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
            exit_code = child.returncode
        except subprocess.TimeoutExpired:
            exit_code = 'timeout_180_seconds'
    results[mod] = exit_code
    command.update(exit_code=exit_code, end=now(), elapsed_seconds=time.monotonic()-start,
                   log_sha256=sha(log), maxrss_bytes_macos_cumulative=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                   output_sha256=sha(output) if output.exists() else None)
    assert all(sha(ROOT / p) == v['sha256'] for p, v in sources.items()), 'source mutation during compilation'
    receipt['commands'].append(command)
    save()
    print('END', mod, exit_code, round(command['elapsed_seconds'], 2), flush=True)
    if exit_code != 0:
        print(log.read_text()[:14000], flush=True)
receipt.update(end=now(), completed_modules=sum(v == 0 for v in results.values()),
               failed_modules=[m for m, v in results.items() if v not in (0, 'blocked')],
               blocked_modules=[m for m, v in results.items() if v == 'blocked'])
save()
print(json.dumps({k: receipt[k] for k in ['completed_modules', 'failed_modules', 'blocked_modules']}), flush=True)

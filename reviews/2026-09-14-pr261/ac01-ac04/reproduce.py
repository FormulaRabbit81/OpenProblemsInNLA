"""Rerun AC-01/AC-04 certificates in disposable copies, preserving the source repo."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', required=True, type=Path)
p.add_argument('--out', required=True, type=Path)
a = p.parse_args()
repo, out = a.repo.resolve(), a.out.resolve()
out.mkdir(parents=True, exist_ok=True)
source = repo / 'references/holden-ac-2026-09-14/submitted'
records = []

def run(name, args, cwd):
    with (out / (name + '.log')).open('w') as log:
        result = subprocess.run([sys.executable, *map(str, args)], cwd=cwd,
                                stdout=log, stderr=subprocess.STDOUT)
    records.append({'name': name, 'exit_code': result.returncode})
    if result.returncode:
        raise RuntimeError(f'{name} failed; inspect {out / (name + ".log")}')

with tempfile.TemporaryDirectory(prefix='ac01-ac04-', dir=out) as scratch:
    scratch = Path(scratch)
    for pack in ['AC01_round3_research_pack', 'AC04_symmetric_extraction']:
        shutil.copytree(source / pack, scratch / pack)
    run('ac01-full-rerun', ['code/verify_all.py', '--output', out / 'ac01-full-rerun.json'],
        scratch / 'AC01_round3_research_pack')
    run('ac04-full-rerun', ['code/run_all.py', '--with-algebra'],
        scratch / 'AC04_symmetric_extraction')
    results = scratch / 'AC04_symmetric_extraction/results'
    shutil.copyfile(results / 'run_all.json', out / 'ac04-full-rerun.json')
    run('independent-checks', [Path(__file__).with_name('independent_checks.py'),
        '--repo', repo, '--out', out / 'independent-checks.json'], scratch)

(out / 'reproduction-status.json').write_text(json.dumps({
    'all_checks_passed': True, 'python': sys.version, 'jobs': records,
    'scope': 'Finite certificate checks; general proof and primary-source review are separate.'
}, indent=2) + '\n')
print('All three audit jobs passed; source repository was read only.')

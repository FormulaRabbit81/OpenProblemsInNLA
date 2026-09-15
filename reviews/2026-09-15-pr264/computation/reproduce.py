"""Rerun the PR264 computational review with a fresh source copy.

Run under the submitted NumPy 2.3.5 / SymPy 1.14.0 pins. No network access or
package installation is performed. --out receives fresh evidence files.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time
import numpy as np
import sympy as sp

parser=argparse.ArgumentParser()
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--out',type=Path,required=True)
args=parser.parse_args()
repo=args.repo.resolve();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
source=repo/'references/mf24-counterexample'
def snapshot():
    return {p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(source.rglob('*')) if p.is_file()}
before=snapshot()
if np.__version__!='2.3.5' or sp.__version__!='1.14.0':
    raise RuntimeError('Use the submitted NumPy 2.3.5 and SymPy 1.14.0 pins')
env={**os.environ,'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'}
record={'reviewed_head':'32b028cf16e210f8f628ab1cc7c8f5b389df0632',
        'reviewed_base':'6d840cd6bdf811e166ba0a07501407fb121ff0ce',
        'source_root':'references/mf24-counterexample','source_sha256':before,
        'python':sys.version,'numpy':np.__version__,'sympy':sp.__version__,
        'platform':platform.platform(),'thread_environment':{k:env[k] for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE')},
        'runs':[]}
def run(command,cwd,log):
    started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
    result=subprocess.run(command,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (out/log).write_text(result.stdout)
    record['runs'].append({'command':command,'log':log,'started_utc':started,
                          'seconds':time.monotonic()-tick,'exit_code':result.returncode})
    if result.returncode:raise RuntimeError(f'Failed {log}: {result.returncode}')
with tempfile.TemporaryDirectory(prefix='mf24-review-',dir=out) as temporary:
    scratch=Path(temporary)/'mf24-counterexample'
    shutil.copytree(source,scratch)
    run([sys.executable,'check_exact.py'],scratch,'original-exact.log')
    run([sys.executable,'check_numeric.py'],scratch,'original-numeric.log')
    run([sys.executable,'independent_check.py','--numeric','--pdf','proof.pdf'],scratch,'submitted-independent.json')
run([sys.executable,str(Path(__file__).with_name('maintainer_check.py')),'--out',str(out/'maintainer-results.json')],out,'maintainer-check.log')
if before!=snapshot():raise RuntimeError('Source changed during review')
record['source_unchanged']=True
(out/'hash-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'source_files':len(before),'source_unchanged':True,'runs':[{k:r[k] for k in ('log','seconds','exit_code')} for r in record['runs']]},indent=2))

#!/usr/bin/env python3
"""Regenerate new certificates and run current and inherited regression checks."""
from __future__ import annotations
import argparse,json,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--with-algebra',action='store_true',help='Also rerun the inherited SymPy matrix audit')
    args=parser.parse_args()
    if not __debug__: raise RuntimeError('Do not run the inherited checks with Python -O')
    prior=ROOT/'prior'/'AC04_continuation';initial=prior/'prior'/'initial'
    jobs=[('new_extraction',[sys.executable,'symmetric_extraction.py'],ROOT/'code'),
          ('new_rigidity',[sys.executable,'verify.py'],ROOT/'code'),
          ('new_tests',[sys.executable,'-m','unittest','-v','test_round4.py'],ROOT/'code'),
          ('prior_25_tests',[sys.executable,'-m','unittest','-v','test_verification.py'],prior/'code'),
          ('initial_8_tests',[sys.executable,'-m','unittest','-v','test_certify.py'],initial/'code')]
    if args.with_algebra:
        jobs.append(('initial_algebra',[sys.executable,'algebra_check.py','--output',str(ROOT/'results'/'inherited_algebra_rerun.json')],initial/'code'))
    records=[];ROOT.joinpath('results').mkdir(exist_ok=True)
    for name,cmd,cwd in jobs:
        start=time.monotonic()
        p=subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (ROOT/'results'/f'{name}_rerun.log').write_text(p.stdout)
        records.append({'name':name,'return_code':p.returncode,'seconds':round(time.monotonic()-start,3)})
        print(f'{name}: {"PASS" if p.returncode==0 else "FAIL"} ({records[-1]["seconds"]}s)',flush=True)
        if p.returncode:
            print(p.stdout);raise SystemExit(p.returncode)
    (ROOT/'results'/'run_all.json').write_text(json.dumps({'status':'PASS','jobs':records,'claim_boundary':'AC-04 equality remains unproved.'},indent=2)+'\n')
    print('All requested checks passed.')
if __name__=='__main__': main()

#!/usr/bin/env python3
"""Recompute all exact round-three certificates, then the retained prior audits."""
from __future__ import annotations
import argparse,hashlib,json,subprocess,sys,tempfile,time,zipfile
from datetime import datetime,timezone
from pathlib import Path
if not __debug__:
    raise RuntimeError('Verification uses assertions; do not run Python with -O.')
ROOT=Path(__file__).resolve().parents[1]

def safe_extract(archive,directory):
    with zipfile.ZipFile(archive) as z:
        if z.testzip() is not None:raise RuntimeError('Archive CRC validation failed.')
        for info in z.infolist():
            target=(directory/info.filename).resolve()
            if not target.is_relative_to(directory.resolve()):raise RuntimeError('Unsafe archive path.')
        z.extractall(directory)

def execute(script,cwd,log,*arguments):
    with log.open('w') as stream:
        result=subprocess.run([sys.executable,'-u',str(script),*arguments],cwd=cwd,
                              stdout=stream,stderr=subprocess.STDOUT,check=False)
    if result.returncode:
        raise RuntimeError(f'{script.name} failed; inspect {log}.')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-prior',action='store_true',help='Only verify the new results; omit inherited bounds/reduction.')
    args=parser.parse_args()
    start=time.time();results=ROOT/'results';results.mkdir(exist_ok=True)
    modules=['section_geometry','pair_geometry','grouped_degeneration','wild_control',
             'cyclic_third_order','toric17_verify','exterior_obstruction','grid_obstruction','test_consistency']
    timings=[]
    for module in modules:
        print('Verifying '+module+'.',flush=True);stage=time.time()
        execute(ROOT/f'code/{module}.py',ROOT,results/f'{module}_verification.log')
        timings.append({'module':module,'seconds':round(time.time()-stage,3),'status':'PASS'})
    print('Independent-prime check for the two cyclic representatives.',flush=True)
    execute(ROOT/'code/exterior_obstruction.py',ROOT,results/'exterior_prime103_verification.log',
            '--representatives-only','--prime','103')
    prior_summary=None;archive=ROOT/'prior/AC03_round2_research_package.zip'
    if not args.skip_prior:
        print('Recomputing the retained round-two and round-one certificates.',flush=True)
        with tempfile.TemporaryDirectory(prefix='ac03_round3_prior_') as temp:
            directory=Path(temp);safe_extract(archive,directory)
            prior=directory/'AC03_round2_verified'
            execute(prior/'code/check_manifest.py',prior,results/'prior_manifest_verification.log')
            execute(prior/'code/verify_all.py',prior,results/'prior_full_verification.log')
            prior_summary=json.loads((prior/'results/full_run_summary.json').read_text())
    summary={'status':'PASS: VERIFIED PARTIAL RESEARCH; AC-03 NOT FULLY SOLVED',
             'finished_utc':datetime.now(timezone.utc).isoformat(),
             'elapsed_seconds':round(time.time()-start,3),
             'python':sys.version,'known_bounds':[17,20],
             'new_numerical_bound':False,'stages':timings,
             'prior_verified':not args.skip_prior,'prior':prior_summary,
             'prior_archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest()}
    (results/'full_run_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(summary['status'],flush=True)
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Instantiate the certified six- or 58-parameter Laderman torus over Q.

Every parameter must be nonzero. The output identity is verified exactly with
verify_candidate.py before it is saved. Use --full for all 58 parameters;
otherwise the six-parameter gauge slice is used. This does not reduce rank.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
from verify_candidate import verify_object
ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--parameters',nargs='+',required=True)
    p.add_argument('--full',action='store_true')
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    torus=json.loads((ROOT/'proofs/laderman_torus.json').read_text())
    cert=torus if args.full else json.loads((ROOT/'proofs/laderman_gauge_slice.json').read_text())
    e=cert['final']['E'] if args.full else cert['slice_E']
    try:pars=[Fraction(x) for x in args.parameters]
    except (ValueError,ZeroDivisionError) as exc:p.error(str(exc))
    dim=58 if args.full else 6
    if len(pars)!=dim or not all(pars):p.error(f'Exactly {dim} nonzero rational parameters required.')
    obj=json.loads((ROOT/'data/laderman23.json').read_text())
    for a,(g,t,k) in enumerate(torus['labels']):
        name=('U','V','W')[g];value=Fraction(obj[name][t][k])
        for z,power in zip(pars,e[a]):value*=z**power
        obj[name][t][k]=str(value)
    obj['name']='laderman_torus_instance'
    obj['parameters']=[str(x) for x in pars]
    obj['parameter_dimension']=dim
    obj['status']='Existing-rank family member, not a lower bound or an improvement to rank 23.'
    result=verify_object(obj)
    if not result['identity_verified']:raise RuntimeError('Exact verification failed; no output written.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'verification':result},indent=2))

if __name__=='__main__':main()

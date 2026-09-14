#!/usr/bin/env python3
"""Run the exact finite checks accompanying the round-three report.

Python 3.10 or later; standard library only. The general tensor constructions
and the all-tree induction are mathematical proofs in the report, not formalized
by this program. The finite certificates are checked without floating point.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
import time
import zipfile

from rational_linear import gram, paired, rank
from noncoordinate import (
    B1, B2, W1, W2, forms_for_odd, split_basis_for_odd,
    verify_core, verify_small_degeneration, verify_literal_retention,
)
from exact_bounds import verify_bound, verify_barrier, verify_finite_mixed_trees

ROOT = Path(__file__).resolve().parents[1]


def read_certificate(name: str) -> dict:
    with (ROOT / 'certificates' / name).open(encoding='utf-8') as f:
        return json.load(f)


def verify_graph_weights(left: int, right: int) -> dict:
    """Check the integer tight weights and exact uniform marginals of Z."""
    weights = list(range(left)) + [left*(j+1) for j in range(right)]
    weights += [-1-i-left*(j+1) for i in range(left) for j in range(right)]
    if len(set(weights)) != len(weights):
        raise AssertionError('Graph weights are not injective')
    weights = [3*w+1 for w in weights]
    for i in range(left):
        for j in range(right):
            if weights[i]+weights[left+j]+weights[left+right+i*right+j] != 0:
                raise AssertionError('A graph triple has nonzero total weight')
    p_a, p_b, p_c = Fraction(1,3*left), Fraction(1,3*right), Fraction(1,3*left*right)
    if left*p_a != Fraction(1,3) or right*p_b != Fraction(1,3):
        raise AssertionError('Wrong group mass')
    if left*p_a+right*p_b+left*right*p_c != 1:
        raise AssertionError('Marginals do not sum to one')
    return {'left': left, 'right': right, 'injective_weights':len(weights),
            'edge_equations_checked':left*right, 'uniform_group_masses':'1/3,1/3,1/3'}


def rerun_prior() -> dict:
    archive = ROOT / 'prior' / 'AC01_round2_research_pack.zip'
    with tempfile.TemporaryDirectory(prefix='ac01_prior_') as td:
        dest = Path(td)
        with zipfile.ZipFile(archive) as z:
            for item in z.infolist():
                p = PurePosixPath(item.filename)
                if p.is_absolute() or '..' in p.parts:
                    raise ValueError('Unsafe archive member')
                if (item.external_attr >> 16) & 0o170000 == 0o120000:
                    raise ValueError('Symbolic links are not accepted')
            z.extractall(dest)
        prior_root = dest / 'AC01_round2_research_pack'
        out = dest / 'prior_result.json'
        cmd = [sys.executable, str(prior_root/'code'/'verify_all.py'), '--output', str(out)]
        run = subprocess.run(cmd, cwd=prior_root, text=True, capture_output=True, timeout=180)
        if run.returncode or 'ALL CHECKS PASSED' not in run.stdout:
            raise AssertionError(f'Prior verification failed:\n{run.stdout}\n{run.stderr}')
        result = json.loads(out.read_text(encoding='utf-8'))
        return {'completed_successfully':True, 'stdout':run.stdout, 'result':result}


def negative_tests(core:dict, seed:dict, bound:dict, barrier:dict) -> list[str]:
    tests=[]
    def rejected(name, fun, arg):
        try:
            fun(arg)
        except (AssertionError, ValueError):
            tests.append(name)
        else:
            raise AssertionError(f'Corrupted certificate accepted: {name}')
    x=deepcopy(core);x['B1'][0][0]='0'
    rejected('changed core form',verify_core,x)
    x=deepcopy(core);x['slices'][0][1][2]='2'
    rejected('changed P slice',verify_core,x)
    x=deepcopy(core);x['split_basis_1'][0][0]='0'
    rejected('changed rational split basis',verify_core,x)
    x=deepcopy(seed);x['rows'][9][0]='2'
    rejected('changed literal head row',verify_small_degeneration,x)
    x=deepcopy(seed);x['row_degrees'][9]=-1
    rejected('changed Laurent head exponent',verify_small_degeneration,x)
    x=deepcopy(bound);x['radicals']['lift_0']['floor_numerator']+=1
    rejected('incorrect cube-root enclosure',verify_bound,x)
    x=deepcopy(bound);x['upper_bound']='969/250'  # 3.876, below the certified boundary
    rejected('unsupported bound 3.876',verify_bound,x)
    x=deepcopy(bound);x['stages'][1]['active_main_dimension']-=1
    rejected('incorrect active dimension',verify_bound,x)
    x=deepcopy(barrier);x['candidate_rho']='183/50'  # 3.66 violates the leaf envelope
    rejected('unsupported tree-envelope candidate 3.66',verify_barrier,x)
    rejected('even lifting parameter',lambda n:forms_for_odd(n,B1),2)
    return tests


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'results'/'verification_rerun.json')
    parser.add_argument('--skip-prior',action='store_true',help='Do not rerun the archived round-two verifier')
    args=parser.parse_args()
    started=time.perf_counter()
    core=read_certificate('isotropic_core.json')
    seed=read_certificate('small_degeneration.json')
    bound=read_certificate('bound.json')
    barrier=read_certificate('tree_envelope.json')
    result={'schema':'ac01-round3-verification-v1','python':sys.version.split()[0],
            'core':verify_core(core),'literal_degeneration':verify_small_degeneration(seed)}
    bases=[]
    for ell in (1,3,5,37):
        for index,(b,w) in enumerate(((B1,W1),(B2,W2)),start=1):
            g=forms_for_odd(ell,b);a=split_basis_for_odd(ell,b,w)
            if gram(a,g)!=paired(3*ell+1):
                raise AssertionError('Lifted split basis failed')
            bases.append({'ell':ell,'form':index,'dimension':3*ell+1,'paired_gram_verified':True})
    result['rational_split_bases']=bases
    pairs=((1,1),(1,3),(3,1),(3,5),(5,7),(37,37))
    result['literal_lift_restrictions']=[verify_literal_retention(a,b) for a,b in pairs]
    result['tight_graph_supports']=[verify_graph_weights(a,b) for a,b in pairs]
    result['bound']=verify_bound(bound)
    result['tree_envelope']=verify_barrier(barrier)
    result['supplementary_finite_trees']=verify_finite_mixed_trees()
    result['adversarial_cases_rejected']=negative_tests(core,seed,bound,barrier)
    result['prior_pack']={'skipped':True} if args.skip_prior else rerun_prior()
    result['all_checks_passed']=True
    result['elapsed_seconds']=round(time.perf_counter()-started,6)
    result['scope_notice']=(
        'Exact finite coefficient, rational-form, and integer-cube checks. '
        'The all-size constructions, all-tree induction, and external spectral theorems '
        'are not proof-assistant formalized. This is not a solution of AC-01.'
    )
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('ALL CHECKS PASSED')
    print('Derived strict CW2 bound:',result['bound']['upper_bound'])
    print('Literal degeneration ordered coefficients covered:',result['literal_degeneration']['all_ordered_coefficients_covered'])
    print('Largest literal retained tensor nonzero coefficients:',result['literal_lift_restrictions'][-1]['target_nonzero_ordered_coefficients'])
    print('All-binary-tree scalar candidate:',result['tree_envelope']['candidate_rho'])
    print('Adversarial cases rejected:',len(result['adversarial_cases_rejected']))
    print('Previous pack rerun:',not args.skip_prior)
    print('Elapsed seconds:',result['elapsed_seconds'])
    print(result['scope_notice'])
    return 0


if __name__=='__main__':
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate exact finite certificates for the accompanying AC-05 report.

Requires SymPy. Infinite-product and geometric arguments are proved in the report;
finite verification is not substituted for those arguments.
"""
from __future__ import annotations
import json
from pathlib import Path
from itertools import product
from math import gcd, lcm
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'certificates'
z = sp.Symbol('z')


def tensor(kind: str, parameter=z):
    if kind == 'U':
        return {v: sp.Integer(1) for v in [(0,0,2),(0,2,1),(1,1,1),(1,2,0),(2,0,1),(2,1,0)]}
    ans = {v: sp.Integer(1) for v in [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1)]}
    ans[(2,1,0)] = sp.sympify(parameter)
    if kind == 'F':
        ans[(1,1,1)] = sp.Integer(1)
    elif kind != 'Q':
        raise ValueError(f'Unknown kind: {kind}')
    return ans


def action(T, modes=(0,1,2)):
    cols = []
    for mode in modes:
        for p,q in product(range(3),repeat=2):
            v = sp.zeros(27,1)
            for ijk,c in T.items():
                if ijk[mode] == q:
                    dest=list(ijk);dest[mode]=p
                    v[9*dest[0]+3*dest[1]+dest[2]] += c
            cols.append(v)
    return sp.Matrix.hstack(*cols)


def coeffs(p):
    p = sp.Poly(sp.expand(p), z)
    if p.is_zero:
        return [0]
    return [int(p.nth(i)) for i in range(p.degree()+1)]


def matrix(M):
    return [[int(M[i,j]) for j in range(M.cols)] for i in range(M.rows)]


def kernel_vectors(kind):
    I=sp.eye(3);Z=sp.zeros(3)
    ks=[(I,-I,Z),(I,Z,-I)]
    if kind == 'F':
        H=sp.diag(-1,0,1);ks.append((H,H,H))
    elif kind == 'Q':
        for H in [sp.diag(1,-1,0),sp.diag(0,1,-1)]:ks.append((H,H,H))
    else:
        ks.append((sp.diag(0,1,2),sp.diag(0,1,2),sp.diag(-3,-2,0)))
    return [[int(x) for M in triple for x in M] for triple in ks]


def minor_certificate(J):
    evaluated=J.subs(z,2)
    rows=list(evaluated.T.rref()[1]);cols=list(evaluated.rref()[1])
    square=J.extract(rows,cols)
    det=sp.factor(square.det(method='domain-ge'))
    if det == 0:raise ArithmeticError('Selected minor is zero')
    return {'rows':rows,'cols':cols,'det_coefficients':coeffs(det),'size':len(rows)}


def primitive_vector(v):
    den=lcm(*(int(t.q) for t in v));out=[int(t*den) for t in v]
    g=gcd(*out)
    return [a//g for a in out]


def build_local():
    data={'schema':1,'variable':'z','families':{}}
    for kind in ['U','F','Q']:
        T=tensor(kind);J=action(T)
        record={
            'terms':[{'index':list(k),'coefficients':coeffs(v)} for k,v in sorted(T.items())],
            'action_constant':matrix(J.subs(z,0)),
            'action_linear':matrix(J.diff(z)),
            'kernels':kernel_vectors(kind),
            'full_minor':minor_certificate(J),
            'pairs':[]}
        for modes in [(0,1),(0,2),(1,2)]:
            rec=minor_certificate(action(T,modes));rec['modes']=list(modes)
            record['pairs'].append(rec)
        assert J*sp.Matrix(record['kernels']).T == sp.zeros(27,len(record['kernels']))
        assert len(record['kernels'])+record['full_minor']['size']==27
        data['families'][kind]=record
        print(kind,'full det',record['full_minor']['det_coefficients'],flush=True)
    data['exceptional']={}
    for kind in ['F','Q']:
        J=action(tensor(kind,-1))
        ks=[primitive_vector(v) for v in J.nullspace()]
        data['exceptional'][kind]={'parameter':-1,'kernels':ks,'full_minor':minor_certificate(J)}
        print(kind,'minus one dimension',len(ks),flush=True)
    return data


def build_constructions():
    cases={}
    for kind in ['F','Q','U']:
        T=tensor(kind)
        As=[sp.Matrix(3,3,lambda j,k:T.get((i,j,k),0)) for i in range(3)]
        S=As[1] if kind=='F' else (As[0]+As[2] if kind=='U' else sum(As,sp.zeros(3)))
        N=As[0]*S.inv();L=(As[2] if kind=='F' else As[1])*S.inv()
        K=sp.simplify(N*L-L*N)
        den=z+1 if kind=='Q' else sp.Integer(1)
        cases[kind]={
            'slice_coefficients':[0,1,0] if kind=='F' else ([1,0,1] if kind=='U' else [1,1,1]),
            'first_other':0,'second_other':2 if kind=='F' else 1,
            'slice_determinant':coeffs(S.det()),
            'commutator_denominator':coeffs(den),
            'commutator_numerator':[[coeffs(sp.cancel(den*K[i,j])) for j in range(3)] for i in range(3)],
            'commutator_numerator_determinant':coeffs(sp.cancel((den*K).det()))}
    return {'schema':1,
            'inversion':{'input_parameter_exponent':3,'output_parameter_exponent':-3,
                'index_permutation':[2,1,0], 'diagonal_exponents':[[0,1,-1],[0,-2,-1],[0,1,-1]]},
            'balanced_to_Q':{'input_even_exponent':0,'input_odd_exponent':1,
                'output_parameter_exponent':3,'diagonal_exponents':[[0,-1,2],[0,0,1],[0,-2,0]]},
            'F_to_Q_weights':[[0,1,-1]]*3,
            'U_nullcone_weights':[[3,0,-3],[3,0,-3],[4,1,-5]],
            'commutators':cases,
            'trace_lift':{
                'X':[[[0,1],[0,0]],[[1,0],[0,1]],[[0,0],[1,0]]],
                'Y_constant':[[[0,1],[0,0]],[[0,0],[0,1]],[[0,0],[1,0]]],
                'Y_linear':[[[0,0],[0,0]],[[1,0],[0,0]],[[0,0],[0,0]]],
                'Z':[[[0,1],[0,0]],[[1,0],[0,1]],[[0,0],[1,0]]]
            }}


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    data={'local.json':build_local(),'constructions.json':build_constructions()}
    for filename,obj in data.items():
        (OUT/filename).write_text(json.dumps(obj,indent=2)+'\n')
    print('Exact certificates generated.')

if __name__=='__main__':main()

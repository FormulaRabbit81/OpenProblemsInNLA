#!/usr/bin/env python3
"""Read and replay finite certificates without third-party packages.

Matrices are independently reconstructed from the stated tensor supports. A
polynomial determinant identity is verified at degree-bound+1 integer nodes,
not by floating-point sampling. The report supplies the all-power and geometric
proofs; this program checks their finite algebraic premises and several powers.
"""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
from itertools import product, permutations
import json
from math import prod
from pathlib import Path
import platform
import time

ROOT=Path(__file__).resolve().parents[1]
P=65521  # prime; modular ranks are rigorous lower bounds on rational ranks
CHECKS=[]
STATS={'determinant_evaluations':0,'power_cases':[]}


def check(condition, message):
    if not condition: raise AssertionError(message)


def group(name, function):
    function();CHECKS.append(name)
    print('PASS',name,flush=True)


def reject_floats(v):
    if isinstance(v,float):raise ValueError('Floating-point certificate value')
    if isinstance(v,dict):
        for x in v.values():reject_floats(x)
    elif isinstance(v,list):
        for x in v:reject_floats(x)


def tensor(kind, parameter=2):
    if kind=='U':return {v:1 for v in [(0,0,2),(0,2,1),(1,1,1),(1,2,0),(2,0,1),(2,1,0)]}
    d={v:1 for v in [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1)]}
    d[(2,1,0)]=parameter
    if kind=='F':d[(1,1,1)]=1
    elif kind!='Q':raise ValueError(kind)
    return {k:v for k,v in d.items() if v!=0}


def poly(c,z):
    value=0
    for a in reversed(c):value=value*z+a
    return value


def action(T,n=3,modes=(0,1,2)):
    M=[[0]*(len(modes)*n*n) for _ in range(n**3)]
    for mode_index,mode in enumerate(modes):
        for ijk,v in T.items():
            for p in range(n):
                dst=list(ijk);dst[mode]=p
                M[(dst[0]*n+dst[1])*n+dst[2]][mode_index*n*n+p*n+ijk[mode]]+=v
    return M


def sparse_action(T,n):
    rows={}
    for ijk,v in T.items():
        for mode in range(3):
            for p in range(n):
                dst=list(ijk);dst[mode]=p
                row=(dst[0]*n+dst[1])*n+dst[2]
                col=mode*n*n+p*n+ijk[mode]
                R=rows.setdefault(row,{})
                R[col]=R.get(col,0)+v
    return rows


def rank_mod(rows,prime=P):
    """Exact sparse row elimination over the indicated prime field."""
    pivots={}
    iterable=rows.values() if isinstance(rows,dict) else rows
    for source in iterable:
        if isinstance(source,dict):r={j:x%prime for j,x in source.items() if x%prime}
        else:r={j:x%prime for j,x in enumerate(source) if x%prime}
        while r:
            j=min(r)
            if j not in pivots:
                inv=pow(r[j],-1,prime)
                pivots[j]={k:v*inv%prime for k,v in r.items()}
                break
            factor=r[j]
            for k,v in pivots[j].items():
                new=(r.get(k,0)-factor*v)%prime
                if new:r[k]=new
                else:r.pop(k,None)
    return len(pivots)


def determinant(A):
    """Fraction-free Bareiss elimination with exact integer divisions."""
    n=len(A)
    check(all(len(row)==n for row in A),'determinant must be square')
    if n==0:return 1
    a=[list(row) for row in A];sign=1;previous=1
    for k in range(n-1):
        q=next((q for q in range(k,n) if a[q][k]),None)
        if q is None:return 0
        if q!=k:a[k],a[q]=a[q],a[k];sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            left=a[i][k]
            for j in range(k+1,n):
                value=a[i][j]*pivot-left*a[k][j]
                check(value%previous==0,'Bareiss division failed')
                a[i][j]=value//previous
            a[i][k]=0
        previous=pivot
    return sign*a[-1][-1]


def transpose(A):return [list(v) for v in zip(*A)]
def mm(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def add(A,B):return [[a+b for a,b in zip(r,s)] for r,s in zip(A,B)]
def sub(A,B):return [[a-b for a,b in zip(r,s)] for r,s in zip(A,B)]
def zero(m,n):return [[0]*n for _ in range(m)]


def inverse(A):
    n=len(A);M=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(n)] for i,row in enumerate(A)]
    for k in range(n):
        q=next((q for q in range(k,n) if M[q][k]),None)
        if q is None:raise ValueError('Singular matrix')
        M[k],M[q]=M[q],M[k]
        p=M[k][k];M[k]=[x/p for x in M[k]]
        for i in range(n):
            if i==k:continue
            t=M[i][k]
            M[i]=[x-t*y for x,y in zip(M[i],M[k])]
    return [row[n:] for row in M]


def verify_minor(kind,rec,modes=(0,1,2),fixed=None):
    r=rec['rows'];c=rec['cols'];n=rec['size'];co=rec['det_coefficients']
    if fixed is not None or kind=='U':check(len(co)==1,'fixed minor must be constant')
    check(len(r)==len(c)==n and len(set(r))==n and len(set(c))==n,'malformed minor')
    check(len(co)<=n+1,'claimed determinant exceeds degree bound')
    # A size-n matrix with affine-linear entries has determinant degree at most n.
    nodes=range(n+1) if fixed is None and kind!='U' else [2]
    for x in nodes:
        M=action(tensor(kind,fixed if fixed is not None else x),modes=modes)
        got=determinant([[M[i][j] for j in c] for i in r])
        check(got==poly(co,x),f'{kind} determinant identity fails at {x}')
        STATS['determinant_evaluations']+=1
    check(any(co),'minor identically zero')


def verify_family(kind,rec):
    for x in [0,1,2,-1]:
        terms={tuple(a['index']):poly(a['coefficients'],x) for a in rec['terms']}
        terms={k:v for k,v in terms.items() if v}
        check(terms==tensor(kind,x),'stored tensor differs from stated support')
        M=action(tensor(kind,x))
        declared=add(rec['action_constant'],[[x*a for a in row] for row in rec['action_linear']])
        check(M==declared,'action matrix mismatch')
        check(mm(M,transpose(rec['kernels']))==zero(27,len(rec['kernels'])),'bad kernel vector')
    check(rank_mod(rec['kernels'])==len(rec['kernels']),'dependent kernel certificate')
    verify_minor(kind,rec['full_minor'])
    check(rec['full_minor']['size']+len(rec['kernels'])==27,'rank/nullity mismatch')
    for p in rec['pairs']:
        check(p['size']==17,'pair map needs rank 17')
        verify_minor(kind,p,tuple(p['modes']))
    # Conciseness follows directly from the free support meeting every index.
    T=tensor(kind,2)
    for mode in range(3):
        check({v[mode] for v in T}=={0,1,2},'missing factor index')
        pairs=[tuple(v[q] for q in range(3) if q!=mode) for v in T]
        check(len(set(pairs))==len(pairs),'not a free support')


def verify_exception(kind,rec):
    M=action(tensor(kind,-1));K=rec['kernels']
    check(mm(M,transpose(K))==zero(27,len(K)),'exception kernel')
    check(rank_mod(K)==len(K),'exception independent kernel')
    verify_minor(kind,rec['full_minor'],fixed=-1)
    check(len(K)+rec['full_minor']['size']==27,'exception rank')


def grouped(T,S,n,p=3):
    ans={}
    for a,u in T.items():
        for b,v in S.items():
            k=tuple(a[i]*p+b[i] for i in range(3))
            ans[k]=ans.get(k,0)+u*v
    return ans


def grouped_cases(spec):
    T={(0,0,0):1};n=1
    for kind,l in spec:T=grouped(T,tensor(kind,l),n);n*=3
    return T,n


def index_word(i,m):
    out=[0]*m
    for q in range(m-1,-1,-1):out[q]=i%3;i//=3
    return out


def word_index(w):
    out=0
    for v in w:out=3*out+v
    return out


def insert_kernel(v,site,m):
    n=3**m;out={}
    for mode in range(3):
        for col in range(n):
            w=index_word(col,m)
            for p in range(3):
                value=v[9*mode+3*p+w[site]]
                if value:
                    ww=list(w);ww[site]=p
                    out[mode*n*n+word_index(ww)*n+col]=value
    return out


def verify_power(spec,local):
    T,n=grouped_cases(spec);m=len(spec);rows=sparse_action(T,n)
    # Two universal scalar relations on the three large factors.
    K=[]
    for other in [1,2]:
        v={}
        for i in range(n):v[i*n+i]=1;v[other*n*n+i*n+i]=-1
        K.append(v)
    for site,(kind,l) in enumerate(spec):
        key=local['exceptional'][kind] if kind in ('F','Q') and l==-1 else local['families'][kind]
        # For generic families the first two vectors are the universal scalars.
        # At exceptional parameters obtain a complement by independence testing.
        selected=[local['families'][kind]['kernels'][0],local['families'][kind]['kernels'][1]]
        for v in key['kernels']:
            if rank_mod(selected+[v])>len(selected):
                selected.append(v);K.append(insert_kernel(v,site,m))
    check(rank_mod(K)==len(K),'product kernel independence')
    for v in K:
        check(all(sum(value*v.get(j,0) for j,value in row.items())==0 for row in rows.values()),'product kernel does not annihilate tensor')
    rank=rank_mod(rows)
    check(rank+len(K)==3*n*n,'product action rank disagrees with theorem')
    traces=[[sum(v.get(mode*n*n+i*n+i,0) for i in range(n)) for v in K] for mode in range(3)]
    sl=len(K)-rank_mod(traces)
    STATS['power_cases'].append({'factors':spec,'factor_dimension':n,'action_rank_mod_65521':rank,'GL_stabilizer_dimension':len(K),'SL_stabilizer_dimension':sl})


def monomial_transform(kind,rec):
    # Coefficients are monomials z^e; all signs here are +1.
    terms={k:(3 if k==(2,1,0) else 0) for k in tensor(kind,2)}
    p=rec['index_permutation'];ds=rec['diagonal_exponents'];got={}
    for ijk,e in terms.items():
        target=tuple(p[v] for v in ijk)
        got[target]=e+sum(ds[q][target[q]] for q in range(3))
    wanted={k:(-3 if k==(2,1,0) else 0) for k in terms}
    check(got==wanted,'inversion monomial identity')


def parity(w):return sum(w[i]>w[j] for i in range(3) for j in range(i+1,3))%2


def verify_balance(rec):
    ds=rec['diagonal_exponents']
    got={w:parity(w)+sum(ds[q][w[q]] for q in range(3)) for w in permutations(range(3))}
    want={w:(3 if w==(2,1,0) else 0) for w in got}
    check(got==want,'balanced normal form scaling')
    check(sum(map(sum,ds))==0,'product determinant must be one')
    for mode in range(3):
        for i in range(3):
            check(sorted(parity(w) for w in got if w[mode]==i)==[0,1],'Gram diagonal not 1+|z|^2')
        pairs=[tuple(w[q] for q in range(3) if q!=mode) for w in got]
        check(len(pairs)==len(set(pairs)),'off-diagonal Gram overlap')


def verify_weights(cons):
    W=cons['F_to_Q_weights']
    check(all(sum(row)==0 for row in W),'F to Q maps not special linear')
    for ijk in tensor('F'):
        value=sum(W[q][ijk[q]] for q in range(3))
        check(value==(3 if ijk==(1,1,1) else 0),'F to Q weight')
    W=cons['U_nullcone_weights'];check(all(sum(row)==0 for row in W),'U maps not special linear')
    check({sum(W[q][v[q]] for q in range(3)) for v in tensor('U')}=={1},'U instability weight')


def verify_cycles(kind,m):
    spec=[(kind,q+2) for q in range(m)];T,n=grouped_cases(spec)
    # Deliberately non-product diagonal scalings on the three grouped factors.
    ds=[[2+i*i+mode*(i+1) for i in range(n)] for mode in range(3)]
    scaled={v:c*prod(ds[mode][v[mode]] for mode in range(3)) for v,c in T.items()}
    for site in range(m):
        num=[];den=[]
        for p in permutations(range(3)):
            words=[[q]*m for q in range(3)]  # other positions fixed at 012
            for q in range(3):words[q][site]=p[q]
            entry=tuple(word_index(w) for w in words)
            (num if parity(p) else den).append(entry)
        for mode in range(3):check(sorted(v[mode] for v in num)==sorted(v[mode] for v in den),'cycle gauge cancellation')
        for arr in [T,scaled]:
            ratio=Fraction(prod(arr[v] for v in num),prod(arr[v] for v in den))
            check(ratio==site+2,'cycle does not recover parameter')


def verify_cubes(m):
    S=list(product([-1,0,1],repeat=m));ss=set(S);count=0
    for columns in product(S,repeat=m):
        A=transpose(columns)
        if determinant(A)==0:continue
        image={tuple(sum(A[i][j]*v[j] for j in range(m)) for i in range(m)) for v in S}
        if image==ss:count+=1
    import math
    check(count==2**m*math.factorial(m),'cube automorphism count')


def verify_triangle_square():
    tri=[(1,0),(0,1),(-1,-1)];S=[a+b for a in tri for b in tri];ss=set(S)
    # Four independent actual character vectors; no presumption about normalizer.
    chosen=[]
    for v in S:
        if rank_mod(chosen+[v])>len(chosen):chosen.append(v)
        if len(chosen)==4:break
    B=inverse(transpose(chosen));count=0
    for images in product(S,repeat=4):
        A=mm(transpose(images),B)
        # A permutation of the full set is automatically invertible, since it spans.
        image={tuple(sum(A[i][j]*v[j] for j in range(4)) for i in range(4)) for v in S}
        if image==ss:count+=1
    check(count==72,'triangle-square automorphism count')


def verify_commutators(cons):
    for kind,rec in cons['commutators'].items():
        for z in range(8):
            T=tensor(kind,z)
            As=[[[T.get((i,j,k),0) for k in range(3)] for j in range(3)] for i in range(3)]
            S=[[sum(rec['slice_coefficients'][i]*As[i][j][k] for i in range(3)) for k in range(3)] for j in range(3)]
            check(determinant(S)==poly(rec['slice_determinant'],z),'slice determinant')
            X=mm(As[rec['first_other']],inverse(S));Y=mm(As[rec['second_other']],inverse(S));K=sub(mm(X,Y),mm(Y,X))
            den=poly(rec['commutator_denominator'],z)
            num=[[poly(v,z) for v in row] for row in rec['commutator_numerator']]
            check([[x*den for x in row] for row in K]==num,'commutator formula')
            check(determinant(num)==poly(rec['commutator_numerator_determinant'],z),'commutator determinant')
    # Characteristic-polynomial identities for the three rank-(3^m-1) cases.
    samples=[('F',1,Fraction(1)),('U',2,Fraction(-1)),('Q',1,Fraction(-3,4))]
    for kind,z,c in samples:
        r=cons['commutators'][kind]
        K=[[Fraction(poly(v,z),poly(r['commutator_denominator'],z)) for v in row] for row in r['commutator_numerator']]
        check(mm(mm(K,K),K)==[[c*x for x in row] for row in K],'K^3 = c K')
        check(rank_mod([[int(v*4) for v in row] for row in K])==2,'rank two commutator')
    for m in range(1,9):
        values=[sum((3**q)*d[q] for q in range(m)) for d in product([-1,0,1],repeat=m)]
        check(len(set(values))==3**m and values.count(0)==1,'balanced ternary distinct eigenvalues')


def verify_trace_lift(rec):
    for z in [-2,-1,0,1,2,5]:
        Y=[add(a,[[z*t for t in row] for row in b]) for a,b in zip(rec['Y_constant'],rec['Y_linear'])]
        got={}
        for i,j,k in product(range(3),repeat=3):
            M=mm(mm(rec['X'][i],Y[j]),rec['Z'][k]);v=sum(M[q][q] for q in range(2))
            if v:got[(i,j,k)]=v
        want=tensor('Q',z)
        if z!=-1:want[(1,1,1)]=1+z
        check(got==want,'trace lift coefficient identity')
    # All entries depend affinely on z, so two nodes already suffice for the identity.


def corruption_tests(local,cons):
    tests=[]
    d=copy.deepcopy(local['families']['F']['full_minor']);d['det_coefficients'][0]+=1
    tests.append(('altered determinant',lambda:verify_minor('F',d)))
    c=copy.deepcopy(cons['inversion']);c['diagonal_exponents'][0][1]+=1
    tests.append(('altered inverse map',lambda:monomial_transform('F',c)))
    b=copy.deepcopy(cons['balanced_to_Q']);b['diagonal_exponents'][0][0]+=1
    tests.append(('altered balanced map',lambda:verify_balance(b)))
    tests.append(('floating certificate',lambda:reject_floats({'value':1.0})))
    for name,fn in tests:
        try:fn()
        except (AssertionError,ValueError):pass
        else:raise AssertionError('Corruption accepted: '+name)


def verify_hypothesis_control():
    D3={(i,i,i):1 for i in range(3)}
    check(rank_mod(action(D3,modes=(0,1)))==15, 'diagonal control pair intersection')
    check(27-rank_mod(action(D3))==6, 'diagonal control base stabilizer')
    D9={(i,i,i):1 for i in range(9)}
    check(243-rank_mod(sparse_action(D9,9))==18, 'diagonal control product stabilizer')
    check(18 != 2+2*(6-2), 'control must fail the formula without its hypothesis')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'results'/'replay.json')
    parser.add_argument('--quick',action='store_true',help='Skip character-configuration enumeration and third powers')
    args=parser.parse_args();started=time.monotonic()
    check(all(P%d for d in range(2,__import__('math').isqrt(P)+1)), 'modulus is not prime')
    local=json.loads((ROOT/'certificates'/'local.json').read_text())
    cons=json.loads((ROOT/'certificates'/'constructions.json').read_text())
    group('integer-only certificate types',lambda:[reject_floats(local),reject_floats(cons)])
    group('scalar-intersection hypothesis: diagonal negative control',verify_hypothesis_control)
    for kind in ['U','F','Q']:
        group(f'{kind}: all-parameter action minors, kernels, scalar pair intersections',lambda kind=kind:verify_family(kind,local['families'][kind]))
    for kind in ['F','Q']:
        group(f'{kind}: exceptional parameter -1',lambda kind=kind:verify_exception(kind,local['exceptional'][kind]))
    cases=[ [('U',2)]*2,[('F',2)]*2,[('F',2),('F',3)], [('Q',2)]*2,[('Q',1)]*2,
           [('F',2),('Q',3)],[('U',2),('F',3)],[('F',-1)]*2,[('Q',-1)]*2 ]
    if not args.quick:cases += [[('F',2)]*3,[('U',2)]*3,[('Q',2)]*3,[('F',2),('Q',3),('U',2)]]
    for spec in cases:
        label=' '.join(k+('' if k=='U' else str(p)) for k,p in spec)
        group('grouped action and trace ranks: '+label,lambda spec=spec:verify_power(spec,local))
    for kind in ['F','Q']:
        group(kind+': explicit reciprocal equivalence',lambda kind=kind:monomial_transform(kind,cons['inversion']))
        for m in [1,2,3]:group(f'{kind}: {m}-factor cycle ratios with arbitrary grouped diagonal gauges',lambda kind=kind,m=m:verify_cycles(kind,m))
    group('balanced representative and three scalar marginals',lambda:verify_balance(cons['balanced_to_Q']))
    group('special-linear F-to-Q limit and U nullcone weights',lambda:verify_weights(cons))
    group('exact commutators and balanced-ternary all-power anchors',lambda:verify_commutators(cons))
    group('27-coefficient trace lift',lambda:verify_trace_lift(cons['trace_lift']))
    if not args.quick:
        group('exhaustive two-dimensional cube automorphisms',lambda:verify_cubes(2))
        group('exhaustive three-dimensional cube automorphisms',lambda:verify_cubes(3))
        group('exhaustive product-of-two-triangles automorphisms',verify_triangle_square)
    group('four deliberately damaged certificates rejected',lambda:corruption_tests(local,cons))
    out={'status':'PASS','check_groups':len(CHECKS),'checks':CHECKS,**STATS,
         'python':platform.python_version(),'elapsed_seconds':round(time.monotonic()-started,3),
         'scope':'Finite algebraic premises and listed powers only. All-power and GIT proofs are in the report; AC-05 is not proved.'}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','check_groups':len(CHECKS),'elapsed_seconds':out['elapsed_seconds']}))

if __name__=='__main__':main()

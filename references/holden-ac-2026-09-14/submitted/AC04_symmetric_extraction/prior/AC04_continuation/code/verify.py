#!/usr/bin/env python3
"""Regenerate finite exact certificates for AC-04 continuation.

Run from any directory: python code/verify.py --output results/verification.json
These checks do NOT prove asymptotic rank three. General theorems also need the
written proofs in report.pdf; external spectral duality is not formalized here.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import time
from exact import (I,U,V,contraction,character_signs,icbrt,kron,kronecker_power,
                   local_h,matmul,power23,pure_factors,rank_exact,rank_mod,
                   sign_matrix,tensor_weights,transpose)

ROOT=Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:raise ArithmeticError(message)


def upper_bound():
    """Independent finite-depth rerun of the inherited sharper upper bound."""
    z=Q('3.923037967879');d,t,M=27,18,72
    p=I.point(z**3)+power23(t);rows=[]
    for j in range(5):
        rows.append({'j':j,'d':d,'t':t,'M':M})
        if j<4:
            dn=d*d+2*d*t;tn=t*t+2*d*d
            p=p.square()-power23(t).square()+power23(tn)
            d,t,M=dn,tn,M*M
            require(t+2*d==M,'Dimension recurrence failed')
    q=p.scale(Q(1,68**16))
    require(q.lo>1,'Inherited strict upper-bound test failed')
    return {'status':'PASS','upper_bound':str(z),'j':4,'theta':'2/3',
            'q4_interval':q.json(),'margin_lower':str(q.lo-1),'dimensions':rows,
            'scope':'Inherited result, not a new improved bound; written spectral argument required'}


def conditional_target():
    """Conditional scalar arithmetic only: the needed decomposition is NOT supplied."""
    z=Q('3.918501');d,t=27,16
    p=I.point(z**3)+power23(t)
    h=I.point(64)+power23(6)
    for _ in range(3):
        dn=d*d+2*d*t;tn=t*t+2*d*d
        p=p.square()-power23(t).square()+power23(tn)
        h=h.square();d,t=dn,tn
    gap=p-h
    require(gap.lo>0,'Conditional scalar endpoint test failed')
    return {'status':'CONDITIONAL_ONLY_REQUIRED_DECOMPOSITION_NOT_SUPPLIED',
            'hypothesis':'A 16-term decomposition of P^2 with a fully supported rank-three contraction',
            'conditional_upper_bound':'3.918501','scalar_margin':gap.json(),
            'scope':'Not an unconditional improvement to asymptotic rank'}


def product_certificates():
    local=[[Q(-1,8),Q(3,8),Q(3,8),Q(3,8)],
           [Q(1),Q(2),Q(3),Q(-6,11)],
           [Q(2),Q(-3),Q(5),Q(-30,11)]]
    for u in local:
        require(sum(1/x for x in u)==0,'Bad harmonic seed')
        require(rank_exact(local_h(u))==2,'Local rank-two test failed')
    examples=[]
    for n in (1,2,3):
        fs=local[:n];w=tensor_weights(fs);A=kronecker_power(U,n)
        M=contraction(A,w)
        r=rank_exact(M)
        require(r==2**n,'Product rank test failed')
        require(pure_factors(w,n) is not None,'Factor reconstruction failed')
        ex={'n':n,'rank':r,'weight_count':len(w)}
        if n>=2:
            wp=w.copy();wp[0]+=1
            require(wp[0]!=0,'Perturbation lost support')
            require(pure_factors(wp,n) is None,'Nonproduct perturbation was accepted')
            rp=rank_exact(contraction(A,wp))
            require(rp==2**n+1,'Sharp rank-gap example failed')
            ex['one_entry_perturbation_rank']=rp
        examples.append(ex)
    # Independence of the four local symmetric matrices and their tensor square.
    for n in (1,2):
        A=kronecker_power(U,n)
        dictionary=[[A[i][r]*A[j][r] for r in range(4**n)]
                    for i in range(3**n) for j in range(3**n)]
        require(rank_exact(dictionary)==4**n,'Contraction dictionary was not injective')
    return {'status':'PASS','exact_rational_examples':examples,'dictionary_ranks':[4,16]}


def sign_certificates():
    results=[]
    for n in (1,2,3):
        minimum=list(character_signs(n));unique=set(map(tuple,minimum))
        require(len(unique)==2*3**n,'Minimum sign count failed')
        for w in minimum:
            require(rank_mod(sign_matrix(w,n))==2**n,'Modular minimum-rank check failed')
            require(pure_factors(w,n) is not None,'Character was not a product')
        near=set()
        if n>=2:
            for w in minimum:
                for j in range(len(w)):
                    wp=w.copy();wp[j]=-wp[j]
                    require(pure_factors(wp,n) is None,'Flipped sign pattern was still a product')
                    require(rank_mod(sign_matrix(wp,n))==2**n+1,'Sharp sign perturbation check failed')
                    near.add(tuple(wp))
            require(len(near)==2*12**n,'Radius-one family count failed')
        results.append({'n':n,'minimum_patterns_checked':len(unique),
                        'rank_of_minimizers':2**n,'single_flip_patterns_checked':len(near),
                        'rank_of_single_flips':2**n+1 if n>=2 else None})
    # Independent direct matrix construction verifies Walsh ordering.
    for n in (1,2,3):
        A=kronecker_power(V,n);w=list(character_signs(n))[0]
        w[0]=-w[0]
        require(contraction(A,w)==sign_matrix(w,n),'Walsh/direct matrix mismatch')
    return {'status':'PASS','prime':101,'checks':results,
            'scope':'Finite checks; exhaustive all-n classification is proved in the report. Single-flip family is not claimed to exhaust the next rank stratum.'}


def adaptive_example():
    """Exact rank-16 decomposition of P^2; nonproduct weights; contraction rank 4."""
    DA=[1,1,1];DB=[1,2,2];Ds=[DA,DB,DA,DB]
    u=[Q(-1,8),Q(3,8),Q(3,8),Q(3,8)]
    v=[Q(-3,32),Q(5,32),Q(15,32),Q(15,32)]
    W=[u,v,[-x for x in u],[-x for x in v]]
    cols=[];cs=[];ws=[]
    for a in range(4):
        D=Ds[a];det=D[0]*D[1]*D[2]
        for b in range(4):
            x=[V[i][a]*D[j]*V[j][b] for i in range(3) for j in range(3)]
            cols.append(x);cs.append([Q(z,16*det) for z in x]);ws.append(W[a][b])
    A=transpose(cols);C=transpose(cs)
    for i,j,k in product(range(9),repeat=3):
        actual=sum(A[i][r]*A[j][r]*C[k][r] for r in range(16))
        expected=int(len({i//3,j//3,k//3})==3 and len({i%3,j%3,k%3})==3)
        require(actual==expected,'Adaptive tensor coefficient identity failed')
    M=contraction(A,ws)
    require(rank_exact(M)==4,'Adaptive contraction rank was not four')
    require(rank_exact(W)==2 and pure_factors(ws,2) is None,'Adaptive weights were not nonproduct')
    MA=contraction(V,u)
    DV=[[DB[i]*x for x in row] for i,row in enumerate(V)]
    MB=contraction(DV,v)
    require(rank_exact(MA)==rank_exact(MB)==2,'Child contractions did not have rank two')
    require(all(sum(row)==0 for row in MA+MB),'Common kernel check failed')
    require(MA!=MB,'Children were accidentally identical')
    return {'status':'PASS','tensor_coefficients_checked':729,'rank_one_terms':16,
            'weight_matrix_rank':2,'contraction_rank':4,'weights':[[str(x) for x in row] for row in W],
            'contraction_matrix':[[str(x) for x in row] for row in M],
            'child_matrices':[[[str(x) for x in row] for row in N] for N in (MA,MB)],
            'scope':'An adaptive nonproduct example attaining four, not an improvement below four'}


def group_membership(x,n):
    for _ in range(n):
        if x%4==0:return False
        x//=4
    return True


def parameters(n,k):
    if not (1<=k<=n):raise ValueError('Require 1 <= k <= n')
    ell=n-k;N=2**ell;a=2**n-2**(ell+1)
    F=4**(n-1)-3**n+2**n+2**(k-1)*3**ell-2**ell
    return N,a,F


def cosets(n,k):
    u=sum(4**i for i in range(n))
    v=sum((2 if i<k else 1)*4**i for i in range(n))
    h=[0,u,v,u^v];seen=set();rows=[]
    for x in range(4**n):
        if x in seen:continue
        orbit=[x^t for t in h];seen.update(orbit)
        occ=[i for i,y in enumerate(orbit) if group_membership(y,n)]
        rows.append((orbit,occ))
    return u,v,rows


def check_cosets(n,k):
    u,v,rows=cosets(n,k);N,a,F=parameters(n,k);ell=n-k
    counts=Counter(len(occ) for _,occ in rows)
    expected={3:N,2:2**n+2**(k-1)*3**ell-3*N,
              1:3**n-2**(n+1)-2**k*3**ell+3*N,0:F}
    for m in range(5):require(counts[m]==expected.get(m,0),'Coset occupancy formula failed')
    pairs=Counter()
    for orbit,occ in rows:
        if len(occ)==2:pairs[orbit[occ[0]]^orbit[occ[1]]]+=1
    require(pairs[u]==pairs[v]==a//2,'Edge multiplicity failed')
    require(pairs[u^v]==2**(k-1)*3**ell-N,'Opposite-pair count failed')
    return {'n':n,'k':k,'N':N,'a':a,'F':F,'cosets':len(rows)}


def block_degeneration(n,k):
    """Exact sparse coefficient/valuation audit of simultaneous extraction maps."""
    u,v,_=cosets(n,k);W={u,v}
    S={x for x in range(4**n) if group_membership(x,n)}
    E={x for x in range(4**n) if x not in S and all((x^w) not in S for w in W)}
    retained=S|E;coeff={}
    # A and B project onto a core copy of S and an auxiliary copy of E.
    # C projects onto core S, together with two new coordinates u,v.
    def add(key,exp,c):
        old=coeff.get((key,exp),0)+c
        if old:coeff[key,exp]=old
        elif (key,exp) in coeff:del coeff[key,exp]
    for a,b in product(retained,repeat=2):
        c=a^b;ia=int(a in E);ib=int(b in E)
        if c in S:add((ia,a,ib,b,0,c),ia+ib,1)
        if c in W:add((ia,a,ib,b,1,c),ia+ib-2,1)
    # Padding K cancels precisely the core/core/new-third blocks.
    for a in S:
        for c in W:
            b=a^c
            if b in S:add((0,a,0,b,1,c),-2,-1)
    require(all(exp>=0 for _,exp in coeff),'A negative-power cross block survived')
    constant={key:c for (key,exp),c in coeff.items() if exp==0}
    expected={}
    for a,b in product(S,repeat=2):
        c=a^b
        if c in S:expected[(0,a,0,b,0,c)]=1
    for a,b in product(E,repeat=2):
        c=a^b
        if c in W:expected[(1,a,1,b,1,c)]=1
    require(constant==expected,'Wrong constant coefficient tensor')
    N,a,F=parameters(n,k)
    core=sum(key[0]==0 for key in constant)
    auxiliary=sum(key[0]==1 for key in constant)
    require(core==6**n and auxiliary==8*F,'Constant support counts failed')
    return {'n':n,'k':k,'core_coefficients':core,'auxiliary_coefficients':auxiliary,
            'positive_degree_terms':sum(exp>0 for _,exp in coeff),
            'degrees_present':sorted(set(exp for _,exp in coeff)),
            'negative_degree_terms':0}


def pencil_local_checks():
    # Three-term border decomposition of the 3x3x2 path pencil.
    p={}
    for j in (1,2):
        for i,e in ((0,0),(j,1)):
            for k,f in ((0,0),(j,1)):
                key=(i,k,j-1,e+f-1);p[key]=p.get(key,0)+1
        key=(0,0,j-1,-1);p[key]=p.get(key,0)-1
    p={key:c for key,c in p.items() if c}
    target={(0,1,0,0):1,(1,0,0,0):1,(0,2,1,0):1,(2,0,1,0):1,
            (1,1,0,1):1,(2,2,1,1):1}
    require(p==target,'Path-pencil border decomposition failed')
    H=[[1,1,1,1],[1,-1,1,-1],[1,1,-1,-1],[1,-1,-1,1]]
    for t in (1,2):
        P=[[int((i^j)==t) for j in range(4)] for i in range(4)]
        diagonal=matmul(matmul(H,P),transpose(H))
        require(diagonal==[[4*H[i][t] if i==j else 0 for j in range(4)] for i in range(4)],
                'Fourier pencil diagonalization failed')
    return {'path_border_terms':3,'path_constant_coefficients':4,'path_error_degree':1,
            'regular_pencil_eigenspace_multiplicities':[2,2]}


def two_slice_certificates():
    enumerated=[check_cosets(n,k) for n in range(1,8) for k in range(1,n+1)]
    sparse=[block_degeneration(n,k) for n,k in ((2,1),(3,1),(3,2),(3,3),(4,1),(4,4))]
    rho=Q(79,20);slacks=[]
    for n in range(1,7):
        for k in range(1,n+1):
            N,a,F=parameters(n,k)
            h=I.point(4**n)+power23(N).scale(3)+power23(a).scale(2)
            p=I.point(rho**n)+power23(2*F).scale(2)
            slack=h-p
            require(slack.lo>0,'The balanced two-slice feasibility check failed')
            slacks.append({'n':n,'k':k,'slack_interval':slack.json()})
    # All n >= 7: omit positive padding and dominate the extracted value by
    # (4/3)*4**(2*n/3). These three rational comparisons prove the tail.
    require(Q(2)<Q(4,3)**3,'Cube-root upper comparison failed')
    require(4**7>24**3,'Tail denominator comparison failed')
    require(1-Q(79,80)**7>Q(1,18),'Tail gap comparison failed')
    return {'status':'PASS','coset_enumeration':enumerated,'sparse_map_checks':sparse,
            'local_pencil_checks':pencil_local_checks(),
            'formal_feasible_value':'79/20','theta_each':'2/3','finite_slacks':slacks,
            'tail_starts_at_n':7,'scope':'The displayed two-character seed inequalities only; not a tensor lower bound or a restriction on all further extraction operations'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'results'/'verification.json')
    args=p.parse_args();out={'status':'FINITE_CHECKS_PASS_AC04_NOT_SOLVED','arithmetic':'integers and rational intervals; modular ranks used only with stated analytic upper bounds'}
    for name,fn in [('inherited_upper',upper_bound),('conditional_target',conditional_target),('fixed_product',product_certificates),
                    ('sign_families',sign_certificates),('adaptive_example',adaptive_example),
                    ('simultaneous_slices',two_slice_certificates)]:
        st=time.monotonic();out[name]=fn();print(f'{name}: PASS ({time.monotonic()-st:.3f} seconds)',flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('AC-04 exact target remains unproved. Finite checks are not a formalization of the general proofs.')

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exact finite checks for the AC-04 local-deformation continuation.
The general analytic and all-power proofs are in report.pdf, not formalized here.
No computation in this file proves asymptotic rank three.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product,combinations_with_replacement
from pathlib import Path
import argparse,json,random,time
from exact import (I,V,U,rational,transpose,matmul,kron,kronecker_power,contraction,
                   rank_exact,rank_mod,rref,nullspace,determinant,inverse2,power23)
ROOT=Path(__file__).resolve().parents[1]
S=list(product(range(1,4),repeat=2))
G=list(product(range(4),repeat=2))
BASIS=[[-1,1,0],[-1,0,1]]

def require(condition,message):
    if not condition:raise ArithmeticError(message)

def char(q,g):
    return -1 if sum((x&y).bit_count() for x,y in zip(q,g))%2 else 1

def charge(triple):
    return tuple(S[triple[0]][k]^S[triple[1]][k]^S[triple[2]][k] for k in range(2))

def charge_block(t):
    triples=[u for u in combinations_with_replacement(range(9),3) if charge(u)==tuple(t)]
    E=[[u.count(q) for q in range(9)] for u in triples]
    return triples,E

def kernel_basis(t):
    out=[]
    if t[1]==0:
        out += [[b[j-1] for i,j in S] for b in BASIS]
    if t[0]==0:
        out += [[b[i-1] for i,j in S] for b in BASIS]
    return out

def tangent_certificate():
    data=[];rank_sum=0;cp_sum=0
    for t in G:
        triples,E=charge_block(t);K=kernel_basis(t)
        e_rank=rank_exact(E);expected=9-len(K)
        require(e_rank==expected,'Wrong symmetric tangent rank')
        if K:
            require(rank_exact(K)==len(K),'Dependent kernel vectors')
            require(all(not x for row in matmul(E,transpose(K)) for x in row),'Wrong kernel formula')
        ordered=[u for u in product(range(9),repeat=3) if charge(u)==t]
        J=[[int(q==u[mode]) for mode in range(3) for q in range(9)] for u in ordered]
        cp_rank=rank_exact(J)
        require(cp_rank==27-len(K)-2,'Wrong unrestricted tangent rank')
        rank_sum+=e_rank;cp_sum+=cp_rank
        data.append({'charge':t,'triples':triples,'E':E,'kernel_basis':K,
                     'rank':e_rank,'unrestricted_charge_rank':cp_rank})
    require((rank_sum,cp_sum)==(128,384),'Wrong total Jacobian ranks')
    return {'status':'PASS','symmetric_jacobian_rank':rank_sum,'symmetric_kernel_dimension':16,
            'unrestricted_jacobian_rank':cp_sum,'unrestricted_kernel_dimension':48,
            'blocks':data}

def obstruction_certificate():
    blocks=[]
    for I_,J_ in product(range(1,4),repeat=2):
        t=(I_,J_);triples,E=charge_block(t)
        K=nullspace(transpose(E))
        Qm=[[sum(a[S[q][0]-1] for q in u)*sum(b[S[q][1]-1] for q in u)
             for a,b in product(BASIS,repeat=2)] for u in triples]
        require(len(K)==4,'Incorrect cokernel dimension')
        require(all(not x for row in matmul(K,E) for x in row),'Cokernel failure')
        M=matmul(K,Qm);det=determinant(M)
        require(det!=0,'The mixed obstruction is not invertible')
        # Independent Fourier summation for every coefficient of each mixed term.
        for u in combinations_with_replacement(range(9),3):
            t0=charge(u)
            for a,b in product(BASIS,repeat=2):
                actual=Q(0)
                for g in G:
                    Ly=sum(a[S[q][0]-1] for q in u)*char((0,J_),g)
                    Lz=sum(b[S[q][1]-1] for q in u)*char((I_,0),g)
                    actual+=Q(char(t0,g)*Ly*Lz,16)
                expected=(sum(a[S[q][0]-1] for q in u)*sum(b[S[q][1]-1] for q in u)) if t0==t else 0
                require(actual==expected,'Mixed Fourier coefficient failed')
        blocks.append({'charge':t,'K':K,'Q':Qm,'KQ':M,'determinant':det})
    require(blocks[0]['determinant']==-1296,'Wrong displayed determinant')
    return {'status':'PASS','number_of_invertible_blocks':9,'total_mixed_equations':36,'blocks':blocks}

def graph_certificate(max_n=3):
    pairs=0
    for n in range(1,max_n+1):
        for t in product(range(4),repeat=n):
            for q,q1 in product(product(range(1,4),repeat=n),repeat=2):
                s=tuple(next(x for x in range(1,4) if x!=(a^c) and x!=(b^c))
                        for a,b,c in zip(q,q1,t))
                require(all(a^b^c for a,b,c in zip(q,s,t)),'First common-neighbor edge missing')
                require(all(a^b^c for a,b,c in zip(q1,s,t)),'Second common-neighbor edge missing')
                pairs+=1
    return {'status':'PASS','powers_checked':list(range(1,max_n+1)),
            'vertex_pairs_checked':pairs,'all_power_basis':'Coordinatewise common-neighbor proof in report'}

def torus_exponents(reverse=False,cp=False):
    # Ten free coordinates: R[b,1],R[b,2] (eight), S[1],S[2] (two).
    rows=[]
    for a,b in G:
        for i,j in S:
            if reverse:a0,b0,i0,j0=b,a,j,i
            else:a0,b0,i0,j0=a,b,i,j
            row=[0]*10
            for k in range(2):
                row[2*b0+k]=(int(i0==k+1)-int(i0==3))
                row[8+k]=(int(j0==k+1)-int(j0==3))
            rows.append(row)
    if not cp:return rows
    out=[]
    for mode in range(3):
        for g in range(16):
            for q in range(9):
                row=rows[9*g+q]+[0]*32
                row[10+2*g]=1 if mode==0 else (-1 if mode==2 else 0)
                row[10+2*g+1]=1 if mode==1 else (-1 if mode==2 else 0)
                out.append(row)
    return out

def torus_certificate():
    A=torus_exponents();B=torus_exponents(True)
    C=torus_exponents(cp=True);D=torus_exponents(True,True)
    ranks=[rank_exact(A),rank_exact(B),rank_exact([a+b for a,b in zip(A,B)]),
           rank_exact(C),rank_exact(D),rank_exact([c+d for c,d in zip(C,D)])]
    require(ranks==[10,10,16,42,42,48],'Wrong branch tangent dimensions')
    for g in range(16):
        require(all(sum(A[9*g+q][k] for q in range(9))==0 for k in range(10)),
                'Leaf product identity failed')
    return {'status':'PASS','exponent_ranks':ranks,'symmetric_intersection_dimension':4,
            'unrestricted_intersection_dimension':36,
            'first_symmetric_exponent_matrix':A,'second_symmetric_exponent_matrix':B}

def target_coefficient(i,j,k):
    return int(all(len({S[i][l],S[j][l],S[k][l]})==3 for l in range(2)))

def standard_certificate():
    X=[[char(q,g) for g in G] for q in S]
    for i,j,k in product(range(9),repeat=3):
        require(Q(sum(X[i][g]*X[j][g]*X[k][g] for g in range(16)),16)==target_coefficient(i,j,k),
                'Standard 16-term identity failed')
    require(rank_exact(X)==9,'Standard frame not concise')
    return {'status':'PASS','tensor_coefficients_checked':729,'X':X}

def adaptive_example():
    # The second copy is expanded first. The first-copy diagonal torus varies by branch b.
    local=[[char((i,),(a,)) for a in range(4)] for i in range(1,4)]
    Rs=[[Q(p),Q(q),Q(1,p*q)] for p,q in [(2,3),(3,5),(5,7),(7,11)]]
    children=[];us=[];inverses=[]
    for R in Rs:
        A=[[r*x for x in row] for r,row in zip(R,local)]
        constraints=[[A[i][a]*sum(A[j][a] for j in range(3)) for a in range(4)] for i in range(3)]
        ks=nullspace(constraints);require(len(ks)==1,'Unexpected child weight freedom')
        u=ks[0];require(all(u),'Child weights lost support')
        M=contraction(A,u);require(rank_exact(M)==2,'Child rank not two')
        require(all(sum(row)==0 for row in M),'Common kernel identity failed')
        B=[row[:2] for row in M[:2]]
        inv=inverse2(B)
        us.append(u);children.append(M);inverses.append(inv)
    inverse_system=[[inverses[b][i][j] for b in range(4)] for i,j in [(0,0),(0,1),(1,1)]]
    cands=nullspace(inverse_system);require(len(cands)==1,'Unexpected inverse-sum nullity')
    c=cands[0];require(all(c),'Outer reciprocal weights lost support')
    weights=[us[b][a]/c[b] for a,b in G]
    X=[[Q(char((i,j),(a,b)))*Rs[b][i-1] for a,b in G] for i,j in S]
    for i,j,k in product(range(9),repeat=3):
        require(sum(X[i][g]*X[j][g]*X[k][g] for g in range(16))/16==target_coefficient(i,j,k),
                'Adaptive tensor identity failed')
    M=contraction(X,weights);require(rank_exact(M)==4,'Adaptive contraction rank was not four')
    W=[weights[4*a:4*a+4] for a in range(4)]
    require(rank_exact(W)>1,'Expected nonproduct example')
    return {'status':'PASS','tensor_coefficients_checked':729,'R':Rs,'X':X,'weights':weights,
            'weight_array_rank':rank_exact(W),'contraction_rank':4,'contraction_matrix':M,
            'child_weights':us,'outer_inverse_coefficients':c}

def support_certificate():
    records=[]
    for w in product((-1,0,1),repeat=4):
        k=sum(x!=0 for x in w);s=rank_exact(contraction(U,w))
        require(k<=s*s,'Local support inequality failed')
        records.append((k,s))
    product_checks=0
    for (k,s),(k1,s1) in product(records,repeat=2):
        require(k*k1<=(s*s1)**2,'Product support inequality failed')
        product_checks+=1
    rng=random.Random(404);A=kron(U,U)
    for _ in range(512):
        w=[rng.choice((-1,0,1)) for _ in range(16)]
        M=contraction(A,w);s=rank_mod([[int(x) for x in row] for row in M]);k=sum(x!=0 for x in w)
        require(k<=s*s,'Nonproduct modular support check failed')
    # A bound supporting first-step optimality is analytic, not inferred from this grid.
    examples=[]
    for n in range(3,7):
        r=4**n;d=3**n
        best=power23(r+2**n-2*d)-power23(2**n)
        for K in sorted({2*d+1,(r+2*d)//2,r-1}):
            if K>=r:continue
            s=__import__('math').isqrt(K)
            if s*s<K:s+=1
            gain=power23(K+s-2*d)-power23(s)
            require(gain.hi<best.lo,'Positive-gain finite comparison failed')
            examples.append({'n':n,'support':K,'rank_lower_integer':s,'strict_gap_lower':best.lo-gain.hi})
    return {'status':'PASS','local_patterns':81,'product_patterns':product_checks,
            'nonproduct_two_copy_modular_checks':512,'positive_gain_examples':examples,
            'scope':'Finite checks supplement, not replace, the all-tree rank proof and analytic monotonicity'}

def inherited_upper():
    z=Q('3.923037967879');d,t=27,18
    p=I.point(z**3)+power23(t)
    for j in range(4):
        dn=d*d+2*d*t;tn=t*t+2*d*d
        p=p.square()-power23(t).square()+power23(tn)
        d,t=dn,tn
    q=p.scale(Q(1,68**16));require(q.lo>1,'Inherited upper-bound certificate failed')
    return {'status':'PASS','upper_bound':str(z),'q4_interval':q.json(),
            'margin_lower':str(q.lo-1),'scope':'INHERITED; no new unconditional numerical improvement'}

def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encode(v) for v in x]
    return x

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'results'/'exact_certificates.json')
    args=parser.parse_args();out={'status':'PASS','claim_boundary':'AC-04 equality and its negation are NOT established.'}
    for name,fn in [('standard',standard_certificate),('tangent',tangent_certificate),
                    ('mixed_obstruction',obstruction_certificate),('common_neighbor',graph_certificate),
                    ('torus_components',torus_certificate),('adaptive_example',adaptive_example),
                    ('support',support_certificate),('inherited_upper',inherited_upper)]:
        start=time.monotonic();out[name]=fn();print(f'{name}: PASS ({time.monotonic()-start:.3f}s)',flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(encode(out),indent=2)+'\n')
    print('All finite exact checks passed. General proofs remain in report.pdf.')
if __name__=='__main__':main()

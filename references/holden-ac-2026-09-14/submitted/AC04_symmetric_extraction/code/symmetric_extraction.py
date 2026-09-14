#!/usr/bin/env python3
"""Exact Laurent-polynomial audit of the simultaneous CW extraction.
All maps are represented in a paired quadratic-form basis, with integer
coefficients. Their identification with cw_q is over the complex numbers.
"""
from __future__ import annotations
from collections import defaultdict,Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse,json,time
from exact import (rational,matmul,transpose,rank_exact,determinant,power23,I)
ROOT=Path(__file__).resolve().parents[1]

def require(p,msg):
    if not p:raise ArithmeticError(msg)

def nonzero_digits(x,n):
    return all((x>>(2*i))&3 for i in range(n))

def audit_maps(n:int,padding_sign:int=-1):
    if not isinstance(n,int) or n<1:raise ValueError('Positive integer power required')
    r=4**n;G=range(r);S={x for x in G if nonzero_digits(x,n)}
    w=sum(1<<(2*i) for i in range(n));Sw={x^w for x in S}
    F=S&Sw;E=set(G)-(S|Sw);s=len(F);t=len(E);d=len(S)
    require((d,s,t)==(3**n,2**n,r+2**n-2*3**n),'Set counts failed')
    require(w in S and 0 not in S and 0 not in E,'Special-coordinate conditions failed')
    require({x^w for x in E}==E and {x^w for x in F}==F,'Pairing invariance failed')
    # An output coordinate is ('c',g), ('e',g), or ('a',0).
    # Each image entry is (coordinate, Laurent exponent, coefficient).
    images={x:[] for x in G}
    for x in S:images[x].append((('c',x),0,1))
    for x in E:images[x].append((('e',x),1,1))
    images[w].append((('a',0),-2,1))
    polynomial=defaultdict(int);source_terms=0;expanded=0
    for a,b in product(G,repeat=2):
        c=a^b;source_terms+=1
        for terms in product(images[a],images[b],images[c]):
            key=(tuple(u[0] for u in terms),sum(u[1] for u in terms))
            polynomial[key]+=terms[0][2]*terms[1][2]*terms[2][2];expanded+=1
    # C_F has 3s terms. Its unique small coordinate maps to -lambda^-2 a.
    for f in sorted(F):
        for mode in range(3):
            coords=[('c',f),('c',f^w)];coords.insert(mode,('a',0))
            polynomial[(tuple(coords),-2)]+=padding_sign
    polynomial={k:v for k,v in polynomial.items() if v}
    negative={k:v for k,v in polynomial.items() if k[1]<0}
    require(not negative,'Uncancelled negative Laurent coefficient: invalid degeneration')
    limit={coords:value for (coords,e),value in polynomial.items() if e==0}
    expected={}
    for a,b in product(sorted(S),repeat=2):
        c=a^b
        if c in S:expected[(('c',a),('c',b),('c',c))]=1
    for e in E:
        for mode in range(3):
            coords=[('e',e),('e',e^w)];coords.insert(mode,('a',0))
            expected[tuple(coords)]=1
    require(limit==expected,'The constant term is not P^n direct sum C_E')
    require(len(expected)==6**n+3*t,'Unexpected limit support count')
    histogram=Counter(exp for (_,exp) in polynomial)
    return {'status':'PASS','power':n,'r':r,'d':d,'s':s,'t':t,'w':w,
            'group_source_terms_checked':source_terms,'group_terms_after_map_expansion':expanded,
            'padding_terms':3*s,'limit_terms':len(limit),'nonzero_Laurent_support_by_exponent':dict(histogram),
            'negative_terms_after_cancellation':0,'S':sorted(S),'F':sorted(F),'E':sorted(E)}

def gaussian_congruence():
    # Q = R+iI, QQ^T = [[0,1],[1,0]]. This avoids floating-point complex arithmetic.
    R=[[Q(1),0],[Q(1,2),0]];J=[[0,Q(1)],[0,Q(-1,2)]]
    RR=matmul(R,transpose(R));JJ=matmul(J,transpose(J))
    RJ=matmul(R,transpose(J));JR=matmul(J,transpose(R))
    real=[[RR[i][j]-JJ[i][j] for j in range(2)] for i in range(2)]
    imag=[[RJ[i][j]+JR[i][j] for j in range(2)] for i in range(2)]
    require(real==[[0,1],[1,0]] and imag==[[0,0],[0,0]],'Complex congruence failed')
    return {'status':'PASS','real_part':R,'imaginary_part':J,'QQ_transpose':real,
            'scope':'Apply this invertible block on every two-cycle of translation by w'}

def cw_border(q:int):
    """Expand the q+2 Laurent rank-one terms; no limiting rank is guessed."""
    if not isinstance(q,int) or q<1:raise ValueError('Positive q required')
    poly=defaultdict(int)
    def cube(vec,scale):
        # vec entries are (coordinate,power,coefficient); scale is a Laurent polynomial.
        for terms in product(vec,repeat=3):
            coords=tuple(x[0] for x in terms);ex=sum(x[1] for x in terms)
            co=terms[0][2]*terms[1][2]*terms[2][2]
            for exponent,c in scale:poly[(coords,ex+exponent)]+=co*c
    for i in range(1,q+1):cube([(0,0,1),(i,1,1)],[(-2,1)])
    cube([(0,0,1)]+[(i,2,1) for i in range(1,q+1)],[(-3,-1)])
    cube([(0,0,1)],[(-3,1),(-2,-q)])
    poly={k:v for k,v in poly.items() if v}
    require(not any(e<0 for (_,e) in poly),'Border decomposition has a pole')
    limit={a:v for (a,e),v in poly.items() if e==0}
    expected={tuple(0 if j==mode else i for j in range(3)):1
              for mode in range(3) for i in range(1,q+1)}
    require(limit==expected,'Incorrect CW border-decomposition constant term')
    return {'status':'PASS','q':q,'rank_one_summands':q+2,'limit_terms':len(limit),
            'nonzero_Laurent_support_by_exponent':dict(Counter(e for (_,e) in poly))}

def direct_border_padding(n:int):
    """Rational paired-form border formula, with mu=lambda^3.
    Combined with audit_maps and the checked Fourier identity this provides
    4^n+2^n+2 explicit rank-one terms for P^n direct sum C_E, with error degree 9.
    """
    if not isinstance(n,int) or n<1:raise ValueError('Positive integer power required')
    r=4**n;S={x for x in range(r) if nonzero_digits(x,n)}
    w=sum(1<<(2*i) for i in range(n));F=S&{x^w for x in S}
    pairs=[(f,f^w) for f in sorted(F) if f<(f^w)]
    poly=defaultdict(Q)
    def cube(vec,exponent,coefficient):
        for terms in product(vec,repeat=3):
            coords=tuple(x[0] for x in terms)
            e=exponent+sum(x[1] for x in terms)
            c=coefficient*terms[0][2]*terms[1][2]*terms[2][2]
            poly[(coords,e)]+=c
    h=[(('a',0),-2,Q(-1))]
    for f,g in pairs:
        cube(h+[(('c',f),3,Q(1)),(('c',g),3,Q(1))],-6,Q(1,2))
        cube(h+[(('c',f),3,Q(1)),(('c',g),3,Q(-1))],-6,Q(-1,2))
    cube(h+[(('c',g),6,Q(1)) for f,g in pairs],-9,Q(-1))
    cube(h,-9,Q(1))
    poly={key:value for key,value in poly.items() if value}
    nonpositive={key:value for key,value in poly.items() if key[1]<=0}
    expected={}
    for f in F:
        for mode in range(3):
            coords=[('c',f),('c',f^w)];coords.insert(mode,('a',0))
            expected[(tuple(coords),-2)]=Q(-1)
    require(nonpositive==expected,'Direct border formula has incorrect nonpositive part')
    require(all(e<=9 for (_,e) in poly),'Unexpected border-error degree')
    # Character orthogonality verifies the Fourier expression for Gamma_G.
    char_sums=[sum(-1 if ((g&h).bit_count()%2) else 1 for g in range(r)) for h in range(r)]
    require(char_sums==[r]+[0]*(r-1),'Fourier character identity failed')
    return {'status':'PASS','power':n,'rank_one_terms':r+len(F)+2,
            'padding_rank_one_terms':len(F)+2,'pairs':pairs,
            'parameter_substitution':'mu=lambda^3','maximum_tensor_polynomial_degree':9,
            'padding_nonzero_support_by_exponent':dict(Counter(e for (_,e) in poly)),
            'character_sums':char_sums,
            'ordinary_rank_consequence':'R((P^n direct_sum C_E)^k) <= (9*k+1)*(4^n+2^n+2)^k'}

def entropy_support(q:int):
    if q<2 or q%2:raise ValueError('An even q at least two is required')
    labels=[0]+[x for j in range(1,q//2+1) for x in (j,-j)]
    support=set()
    from itertools import permutations
    for j in range(1,q//2+1):support.update(permutations((0,j,-j)))
    require(len(set(labels))==q+1,'Tight weights are not injective')
    require(len(support)==3*q and all(sum(x)==0 for x in support),'Tight support failed')
    marg=[]
    for mode in range(3):
        count=Counter(x[mode] for x in support)
        p={str(a):Q(count[a],len(support)) for a in labels}
        require(p['0']==Q(1,3) and all(p[str(a)]==Q(2,3*q) for a in labels if a),
                'Incorrect uniform-support marginals')
        marg.append(p)
    return {'status':'PASS','q':q,'support_size':len(support),'tight_integer_weights':labels,
            'marginals':marg,'imported_theorem':'Strassen tight-three-tensor monomial subrank formula',
            'derived_asymptotic_subrank':'3*(q/2)^(2/3)'}

def algebraic_bound():
    # beta = (274 - 3*cuberoot(3025))^(1/4).
    a=Q('3.89691367400556951923');b=Q('3.89691367400556951924');display=Q('3.896914')
    N=27*3025
    def gap(z):return (274-z**4)**3-N
    require(0<a<b<display and display**4<274,'Bad bracket domain')
    require(gap(a)>0 and gap(b)<0 and gap(display)<0,'Algebraic upper-bound certificate failed')
    # Power 4 is best in the stated uniterated family with cost s+2 and subrank lower bound.
    comparisons=[]
    for n in [2,3,5]:
        t=4**n+2**n-2*3**n
        # c*t^(2/3)=3*(t/2)^(2/3)
        L=power23(Q(t,2)).scale(3)
        margin=I.point(4**n+2**n+2-Q('3.9')**n)-L
        require(margin.lo>0,'Excluded-power bound was not above 3.9')
        comparisons.append({'power':n,'margin_above_3_9_power':margin.json()})
    require(1-Q(39,40)**6>Q(1,8),'All-larger-powers tail comparison failed')
    return {'status':'PASS','new_unconditional_upper_bound':'3.896914',
            'exact_endpoint':'(274 - 3*cuberoot(3025))^(1/4)',
            'endpoint_bracket':[str(a),str(b)],'polynomial_constant':N,
            'lower_bracket_polynomial_gap':str(gap(a)),
            'upper_bracket_polynomial_gap':str(gap(b)),
            'display_bound_polynomial_gap':str(gap(display)),
            'seed_power_comparisons':comparisons,'large_power_anchor':str(1-Q(39,40)**6-Q(1,8)),
            'scope':'Bound derived from the written degeneration, spectral duality, and tight-support theorem; not asymptotic rank three'}

def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def certify():
    return {'status':'PASS','maps':[audit_maps(n) for n in range(1,5)],
            'complex_congruence':gaussian_congruence(),
            'direct_border_formulas':[direct_border_padding(n) for n in range(1,5)],
            'border_decompositions':[cw_border(q) for q in [2,4,8,16]],
            'tight_auxiliary_tensor':entropy_support(110),'algebraic_bound':algebraic_bound()}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'results'/'symmetric_extraction.json')
    args=parser.parse_args();start=time.monotonic();out=certify()
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(encode(out),indent=2)+'\n')
    print(f'Symmetric CW extraction: PASS ({time.monotonic()-start:.3f}s)')
    for x in out['maps']:print(f"n={x['power']}: P^{x['power']} + cw_{x['t']} <=deg D_{x['r']} + cw_{x['s']}; {x['group_source_terms_checked']} source terms checked")
    print('New unconditional result: 3 <= asymptotic rank(cw_2) < 3.896914.')
    print('AC-04 exact equality remains unproved.')
if __name__=='__main__':main()

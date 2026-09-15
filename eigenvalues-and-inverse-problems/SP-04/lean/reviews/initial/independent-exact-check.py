#!/usr/bin/env python3
"""Independent exact SP-04 arithmetic diagnostics; not a Lean proof."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json,sys

def det(A):
    A=[list(map(F,r)) for r in A]; ans=F(1)
    for j in range(len(A)):
        i=next((i for i in range(j,len(A)) if A[i][j]),None)
        if i is None:return F(0)
        if i!=j:A[j],A[i]=A[i],A[j];ans=-ans
        a=A[j][j];ans*=a
        for i in range(j+1,len(A)):
            t=A[i][j]/a
            for k in range(j+1,len(A)):A[i][k]-=t*A[j][k]
    return ans

def kron(A,B):
    return [[a*B[k][l] for a in row for l in range(len(B[0]))] for row in A for k in range(len(B))]

def K(s,c):
    T=[[[a,-c],[F(1),F(0)]] for a in s]
    return kron(kron(T[0],T[1]),T[2])

def shift(A,z):return [[x-z*(i==j) for j,x in enumerate(row)] for i,row in enumerate(A)]
def eliminate(s,c):
    A=K(s,c)
    return det(shift(A,1))*det(shift(A,-1))

def fmt(x):return str(F(x))
def ser(x):
    if isinstance(x,F):return fmt(x)
    if isinstance(x,list):return [ser(a) for a in x]
    if isinstance(x,dict):return {k:ser(v) for k,v in x.items()}
    return x

lo,hi,cut=F(7,4),F(44,25),F(13,25)
s0=[F(a,1000) for a in [1751,1755,1759]]
endpoints=[1750,1752,1754,1756,1758,1760]
vals=[F(1) for _ in endpoints]
for i,e in enumerate(endpoints):
    t=F(e,1000)**2
    for a in s0:vals[i]*=t-a*a
assert [(v>0)-(v<0) for v in vals]==[-1,1,1,-1,-1,1]

# New auxiliary witness is rational and lies inside the complete source family.
t=F(199,400);x=[-F(1000000,2003*2007),F(2003,1000),F(2007,1000)]
s=[a-t/a for a in x];c=-t
assert lo<s[0]<s[1]<s[2]<hi and 0<t<cut
assert x[0]*x[1]*x[2]==-1
assert all(a*(b-a)==c for a,b in zip(x,s))
y=[abs(a) for a in x]
dx=sum((a-b)**2 for a,b in zip(s,x));dy=sum((a-b)**2 for a,b in zip(s,y))
assert y[0]*y[1]*y[2]==1 and dx-dy==4*s[0]*abs(x[0]) and dx>dy
companion=K(s,c)
v=[x[0]**(1-a)*x[1]**(1-b)*x[2]**(1-d) for a,b,d in product(range(2),repeat=3)]
assert v[-1]==1
assert [sum(a*b for a,b in zip(row,v)) for row in companion]==[-a for a in v]
assert eliminate(s,c)==0
for sig in [s0,s]:
    prod_s=sig[0]*sig[1]*sig[2]
    assert eliminate(sig,0)==1-prod_s**2 and eliminate(sig,0)!=0

constants={
 'positive_discriminant_lower':lo**2-4*cut,
 'sqrt_lower':F(99,100),
 'discriminant_minus_sqrt_lower_squared':lo**2-4*cut-F(99,100)**2,
 'rationalized_sqrt_difference_factor':(2*hi)/(2*F(99,100)),
 'large_root_difference_bound':(1+F(16,9))/2*(hi-lo),
 'root_difference_relaxed_bound':F(1,50),
 'positive_branch_product_upper':cut*hi*F(51,50),
 'positive_branch_product_margin':1-cut*hi*F(51,50),
 'negative_quarter_root_test':F(1,16)+hi/4,
 'negative_quarter_root_margin':cut-(F(1,16)+hi/4),
 'negative_positive_root_test':4-2*lo-cut,
}
assert constants['positive_discriminant_lower']==F(393,400)
assert constants['discriminant_minus_sqrt_lower_squared']>0
assert constants['large_root_difference_bound']==F(1,72)<F(1,50)
assert constants['positive_branch_product_upper']==F(14586,15625)<1
assert constants['negative_quarter_root_margin']==F(7,400)>0
assert constants['negative_positive_root_test']==-F(1,50)

report={
 'scope':'Exact rational diagnostics only. No proof of genericity, all stationary pairs, or Lean verification.',
 'source_diagonal':s0,
 'open_gram_intervals':[[F(a,1000)**2,F(b,1000)**2] for a,b in zip(endpoints[::2],endpoints[1::2])],
 'six_gram_characteristic_values':vals,
 'six_gram_characteristic_numerators_over_10_to_18':[int(v*10**18) for v in vals],
 'six_signs':[-1,1,1,-1,-1,1],
 'auxiliary_rational_witness':{'data':s,'stationary_diagonal':x,'multiplier':c,'improving_diagonal':y,
  'selected_distance_squared':dx,'improved_distance_squared':dy,'strict_improvement':dx-dy,
  'eliminant_at_multiplier':eliminate(s,c),'eliminant_at_zero':eliminate(s,0)},
 'exact_scalar_constants':constants,
 'companion_matrix':companion,
 'companion_eigenvector':v,
}
source_roots=[p for p in Path(__file__).resolve().parents if (p/'problem_ids.json').is_file()]
if source_roots:
    base=source_roots[0]
elif len(sys.argv)==2 and (Path(sys.argv[1])/'problem_ids.json').is_file():
    base=Path(sys.argv[1]).resolve()
else:
    raise SystemExit('Run from the retained repository location, or pass the source repository root as the sole argument.')
paths=['eigenvalues-and-inverse-problems/SP-04/README.md','eigenvalues-and-inverse-problems/SP-04/solution.md','eigenvalues-and-inverse-problems/SP-04/solution.tex','references/colbrook-2026-09-11/verification/reviews/SP-04-review.md']
report['immutable_source_sha256']={p:hashlib.sha256((base/p).read_bytes()).hexdigest() for p in paths}
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(ser(report),indent=2)+'\n')
print('PASS: six strict Gram-characteristic signs, rational interior stationary/improving witness, companion eliminant and exact scalar bounds.')
print('Rational data:',*[str(a) for a in s])
print('Gram sign numerators /10^18:',report['six_gram_characteristic_numerators_over_10_to_18'])

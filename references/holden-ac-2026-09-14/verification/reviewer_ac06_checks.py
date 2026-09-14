"""Independent reviewer reconstruction, 2026-09-14. No submitted modules imported."""
import json
from pathlib import Path
from itertools import combinations,product
from math import comb, factorial, prod
import numpy as np
root=Path(__file__).parent/'AC06_round4'
prime=65521
for n in range(2,10):
    cert=json.loads((root/'evidence'/f'shifted_n{n}_p65521.json').read_text())
    p=(n-1)//2
    cols=list(combinations(range(n),p)); rows=list(combinations(range(n),p+1))
    mat=np.zeros((len(rows)*n,len(cols)*n),dtype=np.int64)
    for a,S in enumerate(rows):
        for b,U in enumerate(cols):
            if set(U)<set(S):
                i=next(iter(set(S)-set(U)))
                sign=(-1)**S.index(i)
                for j in range(n):
                    for k in range(n):
                        mat[a*n+k,b*n+j]=sign*pow(2,n*n*(i*j+i*k+j*k)+i*j*k,prime)%prime
    minor=mat[np.ix_(cert['minor_rows'],cert['minor_columns'])].copy()
    det=1
    for q in range(len(minor)):
        pivot=next((r for r in range(q,len(minor)) if minor[r,q]),None)
        assert pivot is not None
        if pivot!=q:
            minor[[q,pivot]]=minor[[pivot,q]]; det=-det
        d=int(minor[q,q]);det=det*d%prime
        for_start=minor[q+1:,q].copy()*pow(d,-1,prime)%prime
        minor[q+1:,q+1:]=(minor[q+1:,q+1:]-for_start[:,None]*minor[q,q+1:])%prime
    assert det
    print('PASS independent signed matrix and minor',n,len(minor),'det',det,flush=True)
for n in range(1,50):
    for t in range(1,n+1):
        for p in range(n-t+1):
            assert comb(n,p+t)*comb(n,p)<=comb(n,t)*comb(n-t,p)**2
print('PASS exterior-block inequality all n <=49')
exps=[(i,j) for i in range(3) for j in range(3-i)]
points=[(0,0),(1,0),(0,1)]
L=3; D=2; U=6; C=24; B=1+U*C**D
out=[sum((-1)**(L-1-h)*comb(B,h)*comb(B-h-1,L-1-h)*s[j] for h,s in enumerate(points)) for j in range(2)]
def ev(coef,pt):return sum(c*pt[0]**i*pt[1]**j for c,(i,j) in zip(coef,exps))
count=0
for coef in product((-1,0,1),repeat=6):
    if any(ev(coef,s) for s in points):
        assert ev(coef,out)!=0;count+=1
assert count==702
print('PASS independent interpolation construction and 702 detected polynomials',out)

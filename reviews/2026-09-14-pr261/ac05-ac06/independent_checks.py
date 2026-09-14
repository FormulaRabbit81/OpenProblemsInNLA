"""Fresh PR261 AC05/AC06 checks; does not import submitted code.

Usage: python independent_checks.py /path/to/references/holden-ac-2026-09-14/submitted
Requires SymPy and NumPy. Finite/algebraic evidence, not asymptotic proofs.
"""
from pathlib import Path
import sys, json
from itertools import product, combinations
from math import comb, factorial, prod, gcd, isqrt
import sympy as sp
import numpy as np

root = Path(sys.argv[1])
lam = sp.Symbol('lambda')

def check(ok, message):
    if not ok:
        raise RuntimeError(message)

def coeffs(kind):
    if kind == 'U':
        return {t: sp.Integer(1) for t in [(0,0,2),(0,2,1),(1,1,1),(1,2,0),(2,0,1),(2,1,0)]}
    out = {t:sp.Integer(1) for t in [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1)]}
    out[2,1,0] = lam
    if kind == 'F': out[1,1,1] = sp.Integer(1)
    return out

def action(kind, modes):
    data = coeffs(kind)
    def entry(row, col):
        i,j,k = row//9, (row//3)%3, row%3
        h,p,q = modes[col//9], (col//3)%3, col%3
        indices = [i,j,k]
        if indices[h] != p: return 0
        indices[h] = q
        return data.get(tuple(indices), 0)
    return sp.Matrix(27, 9*len(modes), entry)

local = json.loads((root/'AC05_power_rigidity/certificates/local.json').read_text())
for kind in ['U','F','Q']:
    item = local['families'][kind]
    matrix = action(kind, [0,1,2])
    kernels = sp.Matrix(item['kernels'])
    check(matrix*kernels.T == sp.zeros(27,kernels.rows), 'AC05 symbolic kernel failure')
    check(kernels.rank() == kernels.rows, 'AC05 dependent local kernels')
    for minor in [item['full_minor'], *item['pairs']]:
        m = action(kind, minor.get('modes', [0,1,2]))
        determinant = sp.factor(m.extract(minor['rows'],minor['cols']).det(method='domain-ge'))
        expected = sum(sp.Integer(c)*lam**i for i,c in enumerate(minor['det_coefficients']))
        check(sp.expand(determinant-expected) == 0, 'AC05 symbolic determinant failure')
        print('PASS symbolic minor',kind,minor.get('modes','full'),minor['size'],determinant,flush=True)
    if kind != 'U':
        ex = local['exceptional'][kind]
        check(matrix.subs(lam,-1).rank() == 27-len(ex['kernels']), 'AC05 exceptional rank')
    slices = [sp.Matrix(3,3,lambda j,k:coeffs(kind).get((i,j,k),0)) for i in range(3)]
    S = slices[1] if kind == 'F' else (slices[0]+slices[2] if kind == 'U' else sum(slices,sp.zeros(3)))
    X = slices[0]*S.inv()
    Y = slices[2 if kind == 'F' else 1]*S.inv()
    K = sp.simplify(X*Y-Y*X)
    if kind == 'F':
        check(K == sp.diag(-1,1-lam,lam), 'F commutator mismatch')
    elif kind == 'U':
        check(K.charpoly().as_expr() == sp.Symbol('lambda')**3+sp.Symbol('lambda'), 'U characteristic mismatch')
    else:
        check(sp.factor(K.det()-lam*(lam-1)/(1+lam)**3) == 0, 'Q determinant mismatch')
        check(K.subs(lam,1).rank() == 2, 'Q1 commutator rank')
    print('PASS exact symbolic slice commutator',kind,'detS=',sp.factor(S.det()),'detK=',sp.factor(K.det()),flush=True)

def detmod(M, p):
    a=np.array(M,dtype=np.int64,copy=True)%p
    check(a.ndim==2 and a.shape[0]==a.shape[1], 'nonsquare minor')
    d=1
    for j in range(len(a)):
        candidates=np.flatnonzero(a[j:,j])
        if not len(candidates):return 0
        k=j+int(candidates[0])
        if k!=j:a[[j,k]]=a[[k,j]];d=-d
        pivot=int(a[j,j]);d=d*pivot%p
        factors=a[j+1:,j].copy()*pow(pivot,-1,p)%p
        a[j+1:,j+1:]=(a[j+1:,j+1:]-factors[:,None]*a[j,j+1:])%p
        a[j+1:,j]=0
    return d%p

prime=65521
check(all(prime%d for d in range(2,isqrt(prime)+1)), 'Not prime')
expected=[2,4,5,8,9,12,12,15]
for n in range(2,10):
    cert=json.loads((root/'AC06_round4/evidence'/f'shifted_n{n}_p65521.json').read_text())
    p=(n-1)//2
    rs=list(combinations(range(n),p+1));cs=list(combinations(range(n),p))
    mat=np.zeros((len(rs)*n,len(cs)*n),dtype=np.int64)
    for a,S in enumerate(rs):
        for b,U in enumerate(cs):
            if set(U)<set(S):
                i=next(iter(set(S)-set(U)));sgn=(-1)**S.index(i)
                for j,k in product(range(n),repeat=2):
                    exponent=n*n*(i*j+i*k+j*k)+i*j*k
                    mat[a*n+k,b*n+j]=sgn*pow(2,exponent,prime)%prime
    check(list(mat.shape)==cert['matrix_shape'], 'AC06 shape mismatch')
    ids,jds=cert['minor_rows'],cert['minor_columns']
    check(len(ids)==len(jds)==cert['rank_mod_prime'] and len(set(ids))==len(ids) and len(set(jds))==len(jds), 'Malformed witness selection')
    minor=mat[np.ix_(ids,jds)]
    determinant=detmod(minor,prime)
    check(determinant!=0, 'AC06 singular minor')
    cost=comb(n-1,p);lower=(len(ids)+cost-1)//cost
    check(lower==expected[n-2]==cert['certified_border_rank_lower_bound'], 'Wrong rank bound')
    # Corrupt the witness by duplicating a row; the exact determinant must reject it.
    damaged=minor.copy();damaged[-1]=damaged[0]
    check(detmod(damaged,prime)==0, 'Singular corruption accepted')
    print('PASS independently reconstructed Koszul minor',n,len(ids),'det',determinant,'BR lower',lower,'duplicate-row rejected',flush=True)

# Independent compaction implementations, no imported submission code.
points=[(0,0),(1,0),(0,1)];N=2;L=3;D=2;H=1
U=comb(N+D,N);C=2**(L-1)*factorial(L);B=max(L,1+U*H*C**D)
interp=[sum((-1)**(L-1-h)*comb(B,h)*comb(B-h-1,L-1-h)*s[j] for h,s in enumerate(points)) for j in range(N)]
bound=U*H;e=bound.bit_length();moduli=[(1+h*factorial(L))**e for h in range(1,L+1)];modulus=prod(moduli)
crt=[sum(s[j]*(modulus//m)*pow(modulus//m,-1,m) for s,m in zip(points,moduli))%modulus for j in range(N)]
exps=[(i,j) for i in range(3) for j in range(3-i)]
def ev(coef,pt):return sum(c*pt[0]**i*pt[1]**j for c,(i,j) in zip(coef,exps))
detected=0
for co in product([-1,0,1],repeat=len(exps)):
    if any(ev(co,s) for s in points):
        check(ev(co,interp)!=0 and ev(co,crt)!=0, 'Compaction lost witness');detected+=1
check(detected==702 and interp==[-11943935,5973696], 'Compaction count/value')
for length in range(1,31):
    bases=[1+h*factorial(length) for h in range(1,length+1)]
    check(all(gcd(x,y)==1 for x,y in combinations(bases,2)), 'Coprime bases')
check(2+2-2*2==0 and 7+7-7*7==-35, 'Curve unsafe-base negative control')
for n in range(1,60):
    for t in range(1,n+1):
        for p in range(n-t+1):
            check(comb(n,p+t)*comb(n,p)<=comb(n,t)*comb(n-t,p)**2, 'Exterior block inequality')
print('PASS independent CRT/interpolation all 702 detected polynomials; 30 coprime base families; unsafe base-two control; exterior blocks through n=59')
print('PASS. Scope: symbolic local algebra and finite certificates; the written proofs supply all-power assertions. AC05 and AC06 remain Open.')

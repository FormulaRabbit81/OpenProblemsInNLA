"""Small exact rational linear algebra; no external dependencies."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product


def matrix(a):
    return [[F(x) for x in row] for row in a]


def zeros(n, m):
    return [[F(0) for _ in range(m)] for _ in range(n)]


def eye(n):
    a=zeros(n,n)
    for i in range(n):a[i][i]=F(1)
    return a


def transpose(a):return [list(x) for x in zip(*a)]


def matmul(a,b):
    if not a:return []
    if len(a[0])!=len(b):raise ValueError('Incompatible matrix dimensions')
    out=zeros(len(a),len(b[0]))
    for i,row in enumerate(a):
        for k,x in enumerate(row):
            if x:
                for j,y in enumerate(b[k]):
                    if y:out[i][j]+=x*y
    return out


def kron(a,b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def blockdiag(a,b):
    return [r+[F(0)]*len(b[0]) for r in a]+[[F(0)]*len(a[0])+r for r in b]


def inverse(a):
    n=len(a)
    if any(len(r)!=n for r in a):raise ValueError('A square matrix is required')
    aug=[r[:]+e for r,e in zip(matrix(a),eye(n))]
    for col in range(n):
        p=next((i for i in range(col,n) if aug[i][col]),None)
        if p is None:raise ValueError('Singular matrix')
        aug[col],aug[p]=aug[p],aug[col]
        z=aug[col][col];aug[col]=[x/z for x in aug[col]]
        for i in range(n):
            if i!=col and aug[i][col]:
                z=aug[i][col];aug[i]=[x-z*y for x,y in zip(aug[i],aug[col])]
    return [r[n:] for r in aug]


def rank(a):
    if not a:return 0
    b=matrix(a);n=len(b);m=len(b[0]);r=0
    for j in range(m):
        p=next((i for i in range(r,n) if b[i][j]),None)
        if p is None:continue
        b[r],b[p]=b[p],b[r]
        z=b[r][j];b[r]=[x/z for x in b[r]]
        for i in range(r+1,n):
            z=b[i][j]
            if z:b[i]=[x-z*y for x,y in zip(b[i],b[r])]
        r+=1
        if r==n:break
    return r


def determinant(a):
    b=matrix(a);n=len(b);ans=F(1)
    for j in range(n):
        p=next((i for i in range(j,n) if b[i][j]),None)
        if p is None:return F(0)
        if p!=j:b[j],b[p]=b[p],b[j];ans=-ans
        z=b[j][j];ans*=z
        for i in range(j+1,n):
            c=b[i][j]/z
            if c:b[i]=[x-c*y for x,y in zip(b[i],b[j])]
    return ans


def gram(a,f,b=None):return matmul(matmul(a,f),transpose(a if b is None else b))


def paired(n):
    if n%2:raise ValueError('The dimension must be even')
    j=zeros(n,n)
    for i in range(n):j[i][i^1]=F(1)
    return j


def encode(a):return [[str(x) for x in row] for row in a]

def decode(a):return matrix(a)


def split_complement(f, isotropic, split_basis):
    """Return an exact paired complement to an isotropic row subspace.

    split_basis consists of rows and must have Gram matrix paired(n).
    Reflections successively move the isotropic rows to paired coordinate axes.
    This routine is used on a 16-dimensional finite certificate, not huge states.
    """
    n=len(f);j=paired(n);basis=matrix(split_basis)
    if gram(basis,f)!=j:raise ValueError('The supplied basis is not hyperbolic')
    if gram(isotropic,f)!=zeros(len(isotropic),len(isotropic)):
        raise ValueError('The supplied space is not isotropic')
    w=matmul(isotropic,inverse(basis));available=list(range(n))
    while w:
        row=w[0]
        h=next((i for i in available if row[i^1]),None)
        if h is None:raise ValueError('Dependent isotropic rows')
        u=row[:];u[h]-=1
        qu=sum(u[i]*u[i^1] for i in range(n))
        if not qu:raise AssertionError('Reflection denominator is zero')
        refl=eye(n)
        for i in available:
            for k in available:
                refl[i][k]-=2*u[i^1]*u[k]/qu
        w=matmul(w,refl);basis=matmul(refl,basis)
        target=[F(int(i==h)) for i in range(n)]
        if w[0]!=target:raise AssertionError('Reflection did not reach its target')
        reduced=[]
        for row in w[1:]:
            z=row[h];rr=[x-z*y for x,y in zip(row,target)]
            if rr[h] or rr[h^1]:raise AssertionError('Orthogonality was lost')
            reduced.append(rr)
        w=reduced;available=[i for i in available if i not in (h,h^1)]
    out=[basis[i] for i in available]
    if gram(out,f)!=paired(len(out)):raise AssertionError('Complement pairing failed')
    if gram(isotropic,f,out)!=zeros(len(isotropic),len(out)):
        raise AssertionError('Complement is not orthogonal')
    return out

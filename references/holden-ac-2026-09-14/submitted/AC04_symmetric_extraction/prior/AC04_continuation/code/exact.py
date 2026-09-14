"""Small exact-arithmetic utilities. No floating point is used in certificates."""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from typing import Sequence


def rational(x: int | Q | str) -> Q:
    if isinstance(x, (float, complex, bool)):
        raise TypeError('Use an integer, Fraction, or rational string, not inexact input')
    return Q(x)


def transpose(a):
    return [list(x) for x in zip(*a)]


def matmul(a, b):
    if not a or not b or len(a[0]) != len(b):
        raise ValueError('Incompatible matrix dimensions')
    bt = transpose(b)
    return [[sum(x*y for x,y in zip(row,col)) for col in bt] for row in a]


def kron(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def kronecker_power(a, n):
    if n < 0: raise ValueError('Negative power')
    out = [[1]]
    for _ in range(n): out = kron(out, a)
    return out


def rank_exact(a):
    if not a: return 0
    b = [[rational(x) for x in row] for row in a]
    m,n = len(b),len(b[0]);r=0
    if any(len(row)!=n for row in b): raise ValueError('Ragged matrix')
    for j in range(n):
        k=next((i for i in range(r,m) if b[i][j]),None)
        if k is None: continue
        b[r],b[k]=b[k],b[r]
        v=b[r][j];b[r][j:]=[x/v for x in b[r][j:]]
        for i in range(r+1,m):
            v=b[i][j]
            if v: b[i][j:]=[x-v*y for x,y in zip(b[i][j:],b[r][j:])]
        r+=1
        if r==m: break
    return r


def rank_mod(a, p=101):
    # The certificate fixes the verified prime 101. This routine is also tested at 103.
    if p not in (101,103,107): raise ValueError('Use one of the supported primes')
    b=[[int(x)%p for x in row] for row in a]
    if any(not isinstance(x,int) for row in a for x in row):
        raise TypeError('Modular rank input must contain integers')
    if not b:return 0
    m,n=len(b),len(b[0]);r=0
    for j in range(n):
        k=next((i for i in range(r,m) if b[i][j]),None)
        if k is None:continue
        b[r],b[k]=b[k],b[r]
        v=pow(b[r][j],-1,p)
        b[r][j:]=[x*v%p for x in b[r][j:]]
        for i in range(r+1,m):
            v=b[i][j]
            if v:b[i][j:]=[(x-v*y)%p for x,y in zip(b[i][j:],b[r][j:])]
        r+=1
        if r==m:break
    return r


U=[[1,0,0,1],[0,1,0,1],[0,0,1,1]]
V=[[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]


def contraction(a, w, b=None):
    if b is None:b=a
    if any(len(row)!=len(w) for row in a+b):raise ValueError('Weight length mismatch')
    return matmul([[rational(x)*rational(y) for x,y in zip(row,w)] for row in a],transpose(b))


def local_h(w):
    if len(w)!=4:raise ValueError('Four local weights required')
    return contraction(U,w)


def tensor_weights(factors):
    out=[Q(1)]
    for f in factors:out=[x*rational(y) for x in out for y in f]
    return out


def pure_factors(w,n):
    """Return (scalar, normalized factors), or None; exact verification, no fitting."""
    w=[rational(x) for x in w]
    if n<1 or len(w)!=4**n:raise ValueError('Incorrect tensor shape')
    if not all(w):return None
    base=w[0]
    fs=[[w[j*4**(n-1-i)]/base for j in range(4)] for i in range(n)]
    if [base*x for x in tensor_weights(fs)]!=w:return None
    return base,fs


def character_signs(n):
    """All 2*3**n minimum sign patterns in the V convention, from the theorem."""
    for labels in product(range(3),repeat=n):
        w=[int(x) for x in tensor_weights([V[j] for j in labels])]
        yield w
        yield [-x for x in w]


def walsh(w):
    out=list(w);m=len(out)
    if m<1 or m&(m-1):raise ValueError('Walsh length must be a power of two')
    h=1
    while h<m:
        for i in range(0,m,2*h):
            for j in range(i,i+h):
                x,y=out[j],out[j+h];out[j],out[j+h]=x+y,x-y
        h*=2
    return out


def sign_matrix(w,n):
    if len(w)!=4**n:raise ValueError('Wrong sign tensor size')
    f=walsh(w)
    codes=[0]
    for _ in range(n):codes=[4*a+b for a in codes for b in (2,1,3)]
    return [[f[a^b] for b in codes] for a in codes]


def icbrt(n):
    if not isinstance(n,int) or n<0:raise ValueError('Nonnegative integer required')
    if n<2:return n
    lo,hi=0,1<<((n.bit_length()+2)//3)
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**3<=n:lo=mid
        else:hi=mid
    return lo


@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q
    def __post_init__(self):
        object.__setattr__(self,'lo',rational(self.lo));object.__setattr__(self,'hi',rational(self.hi))
        if self.lo>self.hi:raise ValueError('Reversed interval')
    @classmethod
    def point(cls,x):return cls(rational(x),rational(x))
    def __add__(self,o):return I(self.lo+o.lo,self.hi+o.hi)
    def __sub__(self,o):return I(self.lo-o.hi,self.hi-o.lo)
    def scale(self,q):
        q=rational(q)
        return I(min(q*self.lo,q*self.hi),max(q*self.lo,q*self.hi))
    def square(self):
        if self.lo>=0:return I(self.lo**2,self.hi**2)
        if self.hi<=0:return I(self.hi**2,self.lo**2)
        return I(0,max(self.lo**2,self.hi**2))
    def json(self):return {'lo':str(self.lo),'hi':str(self.hi)}


def power23(x, digits=70):
    x=rational(x)
    if x<0 or digits<0:raise ValueError('Nonnegative arguments required')
    D=10**digits;y=x*x*D**3;k=icbrt(y.numerator//y.denominator)
    lo=Q(k,D)
    if lo**3==x*x:return I.point(lo)
    hi=Q(k+1,D)
    if not (lo**3<x*x<hi**3):raise ArithmeticError('Invalid cube-root enclosure')
    return I(lo,hi)

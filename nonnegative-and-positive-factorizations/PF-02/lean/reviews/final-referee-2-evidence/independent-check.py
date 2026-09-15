from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib, json

# A separate referee reconstruction, with no submitted checker imports.
def transpose(A): return [list(v) for v in zip(*A)]
def mul(A,B): return [[sum(a*b for a,b in zip(r,c)) for c in transpose(B)] for r in A]
def det(A):
    n=len(A); total=Q(0)
    for p in permutations(range(n)):
        term=Q((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)))
        for i in range(n): term*=A[i][p[i]]
        total+=term
    return total
def trace(A):return sum(A[i][i] for i in range(len(A)))
positions=[(0,0),(1,1),(2,2),(0,1),(0,2),(1,2)]
def factors(sign):
    result=[]
    for k,(a,b) in enumerate(positions):
        A=[[Q(2*(i==j)) for j in range(3)] for i in range(3)]
        if a==b: A[a][a]+=2
        else: A[a][b]=A[b][a]=Q(sign if k==3 else 1)
        result.append(A)
    return result
expected=[[24,20,20,16,16,16],[20,24,20,16,16,16],[20,20,24,16,16,16],
          [16,16,16,14,12,12],[16,16,16,12,14,12],[16,16,16,12,12,14]]
records=[]
for sign in [1,-1]:
    Fs=factors(sign)
    M=[[trace(mul(A,B)) for B in Fs] for A in Fs]
    assert M==expected
    U=[[A[a][b] for a,b in positions] for A in Fs]
    assert det(U)==32*sign
    margins=[]
    for k,A in enumerate(Fs):
        assert A==transpose(A)
        a,b=positions[k]
        if a==b:
            sos=[[Q(2*(i==j)+2*(i==j==a)) for j in range(3)] for i in range(3)]
        else:
            eps=sign if k==3 else 1
            linear=[Q((i==a)+eps*(i==b)) for i in range(3)]
            other=next(i for i in range(3) if i not in [a,b])
            sos=[[Q(i==j)+linear[i]*linear[j]+Q(i==j==other) for j in range(3)] for i in range(3)]
        assert A==sos
        minors=[det([row[:k] for row in A[:k]]) for k in [1,2,3]]
        assert all(v>0 for v in minors)
        margins.append(list(map(str,minors)))
    records.append({'sign':sign,'factor_determinants':margins,'coordinate_det':str(det(U))})
assert det(expected)==8192
assert min(map(min,expected))==12

# Independently construct the actual symmetric-coordinate congruence map as
# sparse integer polynomials in nine algebraically independent matrix entries.
zero=(0,)*9
def atom(i):
    a=list(zero);a[i]=1;return {tuple(a):1}
def add(A,B):
    C=dict(A)
    for m,c in B.items():C[m]=C.get(m,0)+c
    return {m:c for m,c in C.items() if c}
def scale(A,s):return {m:c*s for m,c in A.items() if c*s}
def product(A,B):
    C={}
    for a,ca in A.items():
        for b,cb in B.items():
            k=tuple(x+y for x,y in zip(a,b));C[k]=C.get(k,0)+ca*cb
    return {k:c for k,c in C.items() if c}
def pdet(A):
    d={0:{zero:1}}; n=len(A)
    for r in range(n):
        new={}
        for mask,p in d.items():
            for c in range(n):
                if mask>>c&1:continue
                sign=(-1)**sum(mask>>j&1 for j in range(c+1,n))
                dest=mask|(1<<c)
                new[dest]=add(new.get(dest,{}),scale(product(p,A[r][c]),sign))
        d=new
    return d[(1<<n)-1]
S=[[atom(3*i+j) for j in range(3)] for i in range(3)]
C=[]
for a,b in positions:
    row=[]
    for i,j in positions:
        q=product(S[a][i],S[b][j])
        if a!=b:q=add(q,product(S[b][i],S[a][j]))
        row.append(q)
    C.append(row)
lhs=pdet(C); rhs={zero:1}
ds=pdet(S)
for _ in range(4):rhs=product(rhs,ds)
assert lhs==rhs
assert len(lhs)==120
assert all(sum(k)==12 for k in lhs)
serial=[{'powers':list(k),'coefficient':v} for k,v in sorted(lhs.items())]
out={'reviewer':'Codex AI agent /root/existing_verification_audit','result':'PASS',
     'method':'Independent standard-library exact rational arithmetic and sparse nine-variable integer polynomial reconstruction',
     'witness_determinant':'8192','minimum_entry':12,'witness_records':records,
     'positive_definiteness_sos_polynomial_identities':12,
     'symbolic_congruence_determinant_equals_fourth_power':True,
     'nonzero_monomials':len(lhs),'polynomial':serial,
     'limitations':'Pre-proof arithmetic diagnostic; not a Lean proof of any topology or quantified factorization statement.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: both full factor tuples, all SPD minors, det M=8192, opposite orientations, exact nine-variable degree-12 determinant identity (120 terms).')

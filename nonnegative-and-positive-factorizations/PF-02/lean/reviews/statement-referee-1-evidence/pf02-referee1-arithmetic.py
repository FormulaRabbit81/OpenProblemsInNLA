"""Independent PF-02 referee arithmetic; no imported author checker or proof code.
OpenAI GPT-6 Codex /root/reference_api_review, 2026-09-15.
Exact arithmetic review evidence only, not a Lean verification.
"""
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import hashlib,json

checks=[]
def check(name,condition):
    assert condition,name
    checks.append(name)

def tr(a): return [list(row) for row in zip(*a)]
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in tr(b)] for row in a]
def det(a):
    a=[[Fraction(v) for v in row] for row in a];n=len(a);d=Fraction(1)
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None:return Fraction(0)
        if pivot!=j:a[pivot],a[j]=a[j],a[pivot];d=-d
        t=a[j][j];d*=t
        for i in range(j+1,n):
            q=a[i][j]/t
            for k in range(j+1,n):a[i][k]-=q*a[j][k]
            a[i][j]=0
    return d
def factors(sign):
    return [[[4,0,0],[0,2,0],[0,0,2]],[[2,0,0],[0,4,0],[0,0,2]],
        [[2,0,0],[0,2,0],[0,0,4]],[[2,sign,0],[sign,2,0],[0,0,2]],
        [[2,0,1],[0,2,0],[1,0,2]],[[2,0,0],[0,2,1],[0,1,2]]]
M=[[24,20,20,16,16,16],[20,24,20,16,16,16],[20,20,24,16,16,16],
   [16,16,16,14,12,12],[16,16,16,12,14,12],[16,16,16,12,12,14]]
coords=[(0,0),(1,1),(2,2),(0,1),(0,2),(1,2)]
def coord(x):return [x[i][j] for i,j in coords]
G=[[([1,1,1,2,2,2][i] if i==j else 0) for j in range(6)] for i in range(6)]
check('all 36 entries strictly positive integers',all(isinstance(v,int) and v>0 for row in M for v in row))
check('ordinary determinant = 8192',det(M)==8192)
orientations=[];principal_minors=[]
for sign in [1,-1]:
    fs=factors(sign);U=[coord(a) for a in fs]
    gram=[[sum(a[i][j]*b[j][i] for i in range(3) for j in range(3)) for b in fs] for a in fs]
    check(f'both-family full trace Gram at sign {sign}',gram==M)
    check(f'coordinate trace metric at sign {sign}',mm(mm(U,G),tr(U))==M)
    check(f'orientation determinant at sign {sign}',det(U)==32*sign)
    orientations.append(int(det(U)))
    for z,a in enumerate(fs):
        minors=[det([row[:t] for row in a[:t]]) for t in [1,2,3]]
        check(f'positive leading minors, sign {sign}, factor {z}',all(v>0 for v in minors))
        check(f'symmetric factor, sign {sign}, factor {z}',tr(a)==a)
        principal_minors.append([int(v) for v in minors])
check('positive sizes below three contradicted by rank bound k²',all(k*k<6 for k in [1,2]))

# Polynomial ring over Z in the nine independent entries of S.
N=9;zero=(0,)*N
def const(v):return {zero:v} if v else {}
def add(a,b):
    out=a.copy()
    for e,c in b.items():
        out[e]=out.get(e,0)+c
        if not out[e]:del out[e]
    return out
def scale(a,c):return {e:v*c for e,v in a.items() if v*c}
def mul(a,b):
    out={}
    for e,c in a.items():
        for f,d in b.items():
            g=tuple(x+y for x,y in zip(e,f));out[g]=out.get(g,0)+c*d
    return {g:v for g,v in out.items() if v}
def power(a,n):
    out=const(1)
    for _ in range(n):out=mul(out,a)
    return out
def var(i):return {tuple(int(j==i) for j in range(N)):1}
def psum(xs):
    out={}
    for x in xs:out=add(out,x)
    return out
def pdet(a):
    out={};n=len(a)
    for p in permutations(range(n)):
        t=const((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)))
        for i,j in enumerate(p):t=mul(t,a[i][j])
        out=add(out,t)
    return out
v=[var(j) for j in range(3)]
norm2=psum(mul(x,x) for x in v)
for sign in [1,-1]:
    for idx,a in enumerate(factors(sign)):
        q=psum(scale(mul(v[i],v[j]),a[i][j]) for i in range(3) for j in range(3))
        if idx<3:
            sos=add(scale(norm2,2),scale(mul(v[idx],v[idx]),2))
        else:
            i,j=[(0,1),(0,2),(1,2)][idx-3]
            k=3-i-j
            pair=add(v[i],scale(v[j],a[i][j]))
            sos=add(norm2,add(mul(pair,pair),mul(v[k],v[k])))
        check(f'all-real positive quadratic form identity, sign {sign}, factor {idx}',q==sos)
S=[[var(3*i+j) for j in range(3)] for i in range(3)]
basis=[]
for i,j in coords:
    b=[[0]*3 for _ in range(3)];b[i][j]=1;b[j][i]=1;basis.append(b)
# Derive the representation from S^T B S, instead of copying the dossier's C.
C=[]
for b in basis:
    transformed=[[psum(scale(mul(S[a][i],S[c][j]),b[a][c]) for a in range(3) for c in range(3))
                  for j in range(3)] for i in range(3)]
    C.append(coord(transformed))
detC=pdet(C);detS4=power(pdet(S),4)
check('symbolic congruence determinant for all nine independent real entries',detC==detS4)
check('symbolic polynomial has 120 terms',len(detC)==120)
# Check the bilinear trace metric on a full basis, hence on every symmetric X,Y.
check('universal symmetric trace coordinate bilinear identity',all(
    sum(basis[a][i][j]*basis[b][j][i] for i in range(3) for j in range(3))==G[a][b]
    for a in range(6) for b in range(6)))
terms=[{'exponents':list(e),'coefficient':c} for e,c in sorted(detC.items())]
record={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review (independent AI)',
    'scope':'Exact arithmetic diagnostics only; topology, full-fiber reasoning and Lean proofs remain separate.',
    'result':'PASS','checks_count':len(checks),'checks':checks,'det_M':8192,
    'orientation_determinants':orientations,'positive_leading_principal_minors':principal_minors,
    'symbolic_congruence_polynomial_terms':terms}
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','checks':len(checks),'symbolic_terms':len(detC),'record_sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))

#!/usr/bin/env python3
"""Exact SP-05 interface diagnostics only; not a universal proof or a Lean certificate."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys

def repository_root():
    if len(sys.argv) == 2:
        root = Path(sys.argv[1]).resolve()
        if (root / 'problem_ids.json').is_file():
            return root
    for root in Path(__file__).resolve().parents:
        if (root / 'problem_ids.json').is_file():
            return root
    raise SystemExit('Pass the repository root when running the external preparation copy.')

def mat(rows): return [[Q(x) for x in row] for row in rows]
def transpose(a): return [list(row) for row in zip(*a)]
def mul(a, b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a, b): return [[x+y for x,y in zip(ra,rb)] for ra,rb in zip(a,b)]
def neg(a): return [[-x for x in row] for row in a]
def scale(a, t): return [[t*x for x in row] for row in a]
def vec(a): return [x for col in zip(*a) for x in col]
def mv(a, x): return [sum(ai*xi for ai,xi in zip(row,x)) for row in a]
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def kron(a,b): return [[a[i][j]*b[k][l] for j in range(len(a[0])) for l in range(len(b[0]))] for i in range(len(a)) for k in range(len(b))]
def det2(a): return a[0][0]*a[1][1]-a[0][1]*a[1][0]
def matrix_unit(i,j): return mat([[int((r,c)==(i,j)) for c in range(2)] for r in range(2)])
def encode(value):
    if isinstance(value,Q): return str(value)
    if isinstance(value,list): return [encode(x) for x in value]
    if isinstance(value,dict): return {k:encode(v) for k,v in value.items()}
    return value

root=repository_root()
paths=[
 'eigenvalues-and-inverse-problems/SP-05/README.md',
 'eigenvalues-and-inverse-problems/SP-05/problem.tex',
 'eigenvalues-and-inverse-problems/SP-05/problem.pdf',
 'eigenvalues-and-inverse-problems/SP-05/solution.md',
 'eigenvalues-and-inverse-problems/SP-05/solution.tex',
 'eigenvalues-and-inverse-problems/SP-05/solution.pdf',
 'references/colbrook-2026-09-11/verification/reviews/SP-05-review.md',
]
hashes={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
source=(root/paths[3]).read_text().replace('\r\n','\n').replace('\r','\n')
block=source[source.index('## Theorem '):source.index('## Scope and review notes')].strip().encode()
assert len(block)==3483
assert hashlib.sha256(block).hexdigest()=='54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42'
registry=json.loads((root/'problem_ids.json').read_text())
assert registry['SP-05']==paths[0]

a=mat([[2,1],[1,2]])
b=mat([[3,0],[0,1]])
k=kron(a,b)
jordan=add(k,kron(b,a))
t=mat([[int(r==((c%2)*2+c//2)) for c in range(4)] for r in range(4)])
assert a==transpose(a) and b==transpose(b)
assert a[0][0]>0 and det2(a)>0 and b[0][0]>0 and det2(b)>0
assert mul(a,b)!=mul(b,a)
assert mul(mul(t,k),t)==kron(b,a)
for i in range(2):
    for j in range(2):
        x=matrix_unit(i,j)
        assert mv(t,vec(x))==vec(transpose(x))
        assert mv(k,vec(x))==vec(mul(mul(b,x),a))
        assert mv(jordan,vec(x))==vec(add(mul(mul(a,x),b),mul(mul(b,x),a)))

symmetric=add(matrix_unit(0,1),matrix_unit(1,0))
skew=add(matrix_unit(0,1),neg(matrix_unit(1,0)))
assert dot(vec(skew),vec(skew))==2
assert transpose(skew)==neg(skew)
sector_values={}
for name,x in [('symmetric',symmetric),('skew',skew)]:
    v=vec(x)
    assert dot(v,mv(jordan,v))==2*dot(v,mv(k,v))
    sector_values[name]=dot(v,mv(k,v))/dot(v,v)

c=mat([[2,1],[1,2]])
x=mat([[-1,0],[0,2]])
y=add(mul(c,x),mul(x,c))
v=[Q(1),Q(0)]
lam=Q(-1)
assert mv(x,v)==[lam*z for z in v]
assert dot(v,mv(y,v))==2*lam*dot(v,mv(c,v))==-4

result={
 'scope':'Optional exact n=2 convention diagnostics only; no finite example proves the full n>=2 theorem.',
 'canonical_id':'SP-05',
 'source_sha256':hashes,
 'historical_proof_block_sha256':hashlib.sha256(block).hexdigest(),
 'historical_proof_block_bytes':len(block),
 'noncommuting_positive_definite_example':{'A':a,'B':b,'A_leading_principal_minors':[a[0][0],det2(a)],'B_leading_principal_minors':[b[0][0],det2(b)]},
 'actual_column_vec_kronecker':{'K_A_tensor_B':k,'J':jordan,'T':t,'four_basis_checks':True},
 'skew_witness':{'W':skew,'column_vec':vec(skew),'frobenius_squared':Q(2)},
 'example_sector_rayleigh_values_not_minima':sector_values,
 'inverse_sylvester_contradiction_identity':{'C':c,'X':x,'Y':y,'lambda':lam,'v':v,'vYv':Q(-4),'two_lambda_vCv':Q(-4)},
 'proposed_kernel_numeric_helper':{'claim':'(0 : Real) < 2','use':'Prove the full-n explicit skew witness has positive squared norm, hence is nonzero and can be normalized for minimum attainment.'},
 'all_checks_passed':True,
}
print(json.dumps(encode(result),indent=2,sort_keys=True))

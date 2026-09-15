"""Independent PF-02 pre-proof arithmetic, using only the Python standard library.

This reconstructs both factorizations and checks the congruence determinant as
an exact polynomial identity in nine indeterminates, not by sampling matrices.
It is a diagnostic, not a Lean proof or a quotient-topology verification.
"""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json


def tr(a):
    return list(map(list, zip(*a)))


def mm(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def det(a):
    a = [list(map(F, row)) for row in a]
    out = F(1)
    for k in range(len(a)):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            out = -out
        d = a[k][k]
        out *= d
        for i in range(k+1, len(a)):
            q = a[i][k]/d
            a[i] = [x-q*y for x, y in zip(a[i], a[k])]
    return out


def coord(a):
    return [a[0][0], a[1][1], a[2][2], a[0][1], a[0][2], a[1][2]]


def encode(a):
    if isinstance(a, F):
        return str(a)
    if isinstance(a, list):
        return [encode(x) for x in a]
    if isinstance(a, dict):
        return {k: encode(v) for k, v in a.items()}
    return a


# A tiny sparse integer polynomial implementation, with an explicit variable count.
def constant(c, n):
    return {(0,)*n: c} if c else {}


def var(i, n):
    p = [0]*n
    p[i] = 1
    return {tuple(p): 1}


def add(a, b):
    c = dict(a)
    for m, q in b.items():
        c[m] = c.get(m, 0)+q
        if c[m] == 0:
            del c[m]
    return c


def scale(q, a):
    return {m: q*c for m, c in a.items() if q*c}


def mul(a, b):
    c = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x+y for x, y in zip(ma, mb))
            c[m] = c.get(m, 0)+ca*cb
    return {m: q for m, q in c.items() if q}


def psum(xs):
    a = {}
    for x in xs:
        a = add(a, x)
    return a


def pmm(a, b):
    return [[psum(mul(x, y) for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def pdet(a, nvars):
    out = {}
    for p in permutations(range(len(a))):
        inversions = sum(p[i] > p[j] for i in range(len(a)) for j in range(i+1, len(a)))
        term = constant((-1)**inversions, nvars)
        for i, j in enumerate(p):
            term = mul(term, a[i][j])
        out = add(out, term)
    return out


I = [[int(i == j) for j in range(3)] for i in range(3)]
factors = []
for i in range(3):
    a = [[2*x for x in row] for row in I]
    a[i][i] += 2
    factors.append(a)
for i, j in [(0, 1), (0, 2), (1, 2)]:
    a = [[2*x for x in row] for row in I]
    a[i][j] = a[j][i] = 1
    factors.append(a)
reflected = [[row[:] for row in a] for a in factors]
reflected[3][0][1] = reflected[3][1][0] = -1
M = [[trace(mm(a, b)) for b in factors] for a in factors]
M2 = [[trace(mm(a, b)) for b in reflected] for a in reflected]
assert M == M2 == [
    [24,20,20,16,16,16], [20,24,20,16,16,16], [20,20,24,16,16,16],
    [16,16,16,14,12,12], [16,16,16,12,14,12], [16,16,16,12,12,14]]
assert min(x for row in M for x in row) == 12
U, U2 = list(map(coord, factors)), list(map(coord, reflected))
G = [[([1,1,1,2,2,2][i] if i == j else 0) for j in range(6)] for i in range(6)]
assert mm(mm(U,G),tr(U)) == M
assert mm(mm(U2,G),tr(U2)) == M
assert det(U) == 32 and det(U2) == -32 and det(G) == 8 and det(M) == 8192
factor_minors = [[det([r[:k] for r in a[:k]]) for k in (1,2,3)]
                 for a in factors+reflected]
assert all(x > 0 for row in factor_minors for x in row)

# Verify explicit positive-definiteness SOS identities in three real variables.
v = [var(i,3) for i in range(3)]
norm2 = psum(mul(x,x) for x in v)
for idx, a in enumerate(factors+reflected):
    qform = psum(scale(a[i][j],mul(v[i],v[j])) for i in range(3) for j in range(3))
    local = idx % 6
    if local < 3:
        sos = add(scale(2,norm2),scale(2,mul(v[local],v[local])))
    else:
        i,j = [(0,1),(0,2),(1,2)][local-3]
        other = next(k for k in range(3) if k not in (i,j))
        signed_pair = add(v[i],scale(a[i][j],v[j]))
        sos = add(add(norm2,mul(signed_pair,signed_pair)),mul(v[other],v[other]))
    assert qform == sos

# Derive the congruence coordinate matrix directly from the six symmetric basis matrices.
n = 9
S = [[var(3*i+j,n) for j in range(3)] for i in range(3)]
basis = []
for i,j in [(0,0),(1,1),(2,2),(0,1),(0,2),(1,2)]:
    a = [[constant(0,n) for _ in range(3)] for _ in range(3)]
    a[i][j] = constant(1,n)
    a[j][i] = constant(1,n)
    basis.append(a)
C = [coord(pmm(pmm(tr(S),a),S)) for a in basis]
detC = pdet(C,n)
detS = pdet(S,n)
detS4 = mul(mul(detS,detS),mul(detS,detS))
assert detC == detS4
assert all(sum(m) == 12 for m in detC)

# All-real-coordinate covariance, not only basis inputs.
nv = 15
SS = [[var(3*i+j,nv) for j in range(3)] for i in range(3)]
x = [var(9+i,nv) for i in range(6)]
X = [[x[0],x[3],x[4]],[x[3],x[1],x[5]],[x[4],x[5],x[2]]]
CC = [[{m+(0,)*6:q for m,q in entry.items()} for entry in row] for row in C]
covariance = coord(pmm(pmm(tr(SS),X),SS))
assert covariance == [psum(mul(x[i],CC[i][j]) for i in range(6)) for j in range(6)]

poly_terms = [[list(m), q] for m,q in sorted(detC.items())]
result = dict(
    status='PASS', scope='Pre-proof exact and symbolic arithmetic; not Lean verification.',
    factors=factors, reflected_factors=reflected, matrix=M, coordinate_matrix=U,
    reflected_coordinate_matrix=U2, trace_metric=G,
    factor_leading_principal_minors=factor_minors,
    determinant_U=det(U), determinant_U_reflected=det(U2),
    determinant_trace_metric=det(G), determinant_M=det(M),
    positivity_sos_identities=12,
    congruence_polynomial=dict(variables=['s11','s12','s13','s21','s22','s23','s31','s32','s33'],
        identity='det C(S) = det(S)^4', degree=12, monomial_count=len(detC),
        exact_terms=poly_terms, covariance_identities=6))
Path(__file__).with_suffix('.json').write_text(json.dumps(encode(result),indent=2)+'\n')
print('PASS: both exact factorizations, positivity SOS, determinants, and '
      'all-nine-variable congruence determinant polynomial identity ('+str(len(detC))+' terms).')

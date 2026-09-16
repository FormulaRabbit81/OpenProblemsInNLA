"""Exact Gaussian-integer polynomial diagnostics, not Lean verification.

No third-party package, approximate arithmetic, root approximation or growing
matrix is used. Two formal variables represent the real parameter and the
complex polynomial argument. These checks support the proposed data only;
the complete parameter/root/Green-kernel theorem still requires Lean proofs.
"""
from itertools import permutations
from pathlib import Path
import json

class P:
    def __init__(self, value=0):
        if isinstance(value, P):
            self.c = value.c.copy()
        elif isinstance(value, dict):
            self.c = {k: v for k, v in value.items() if v != (0, 0)}
        else:
            self.c = {} if value == 0 else {(0, 0): (value, 0)}
    def __add__(self, other):
        out = self.c.copy()
        for k, (a, b) in P(other).c.items():
            c, d = out.get(k, (0, 0)); out[k] = (a+c, b+d)
        return P(out)
    __radd__ = __add__
    def __neg__(self): return P({k: (-a, -b) for k, (a, b) in self.c.items()})
    def __sub__(self, other): return self + -P(other)
    def __rsub__(self, other): return P(other) + -self
    def __mul__(self, other):
        out = {}
        for (j, k), (a, b) in self.c.items():
            for (u, v), (c, d) in P(other).c.items():
                old_re, old_im = out.get((j+u, k+v), (0, 0))
                out[j+u, k+v] = (old_re+a*c-b*d, old_im+a*d+b*c)
        return P(out)
    __rmul__ = __mul__
    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out = P(1)
        for _ in range(n): out = out * self
        return out
    def __eq__(self, other): return self.c == P(other).c
    def conj_coeff(self): return P({k: (a, -b) for k, (a, b) in self.c.items()})

def det(M):
    n = len(M); out = P(0)
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n))
        term = P((-1)**inversions)
        for i in range(n): term = term * M[i][perm[i]]
        out = out + term
    return out

def mm(A, B):
    return [[sum((A[i][k]*B[k][j] for k in range(len(B))), P(0))
             for j in range(len(B[0]))] for i in range(len(A))]

def evaluate(coeff, x):
    return sum((a*x**j for j, a in enumerate(coeff)), P(0))

r=P({(1,0):(1,0)}); z=P({(0,1):(1,0)}); I=P({(0,0):(0,1)})
A=-r-6*I; B=-7*r-30*I; C=7*r-30*I
D=-25*r-30*I; E=r-6*I; F=25*r-30*I
a=30-r**2-10*I*r; b=24*r**2+80*I*r-240; c=420-46*r**2
N=a+(-120-r**2+22*I*r)*z+2*(r**2+18)*z**2
d=a+b*z+c*z**2+b.conj_coeff()*z**3+a.conj_coeff()*z**4
qcoef=[-a.conj_coeff(),-a.conj_coeff()-b.conj_coeff(),a+b,a]
p=a*z**4+b*z**3+c*z**2+b.conj_coeff()*z+a.conj_coeff()
q=evaluate(qcoef,z)
L=[[A,B],[B,D]]; scale=24*a
U=mm([[D,-B],[-B,A]],[[24*r,-96*I,-F,-C],[-96*I,-24*r,-C,-E]])
Tnum=U+[[scale,P(0),P(0),P(0)],[P(0),scale,P(0),P(0)]]
M=[[((scale if i==j else P(0))-z*Tnum[i][j]) for j in range(4)] for i in range(4)]
Rcoef=[15*r,5*(r**2-6),25*r,6*(r**2-10)]
R=evaluate(Rcoef,z)
ca,cb,cc,cd=Rcoef[3],Rcoef[2],Rcoef[1],Rcoef[0]
discr=cb**2*cc**2-4*ca*cc**3-4*cb**3*cd-27*ca**2*cd**2+18*ca*cb*cc*cd
h=[B,96*I,C]; ell=[D,24*r,E]
resultant=(h[2]*ell[0]-h[0]*ell[2])**2-(h[2]*ell[1]-h[1]*ell[2])*(h[1]*ell[0]-h[0]*ell[1])
checks={
    'leading_block_determinant': det(L)==24*a,
    'full_4x4_resolvent_determinant_cleared': det(M)==24**4*a**3*d,
    'full_3x3_boundary_cofactor_cleared': det([row[1:] for row in M[1:]])==24**3*a**2*N,
    'quartic_factorization': p==(z-1)*q,
    'quotient_at_one': evaluate(qcoef,P(1))==120*I*r,
    'quotient_at_minus_one': evaluate(qcoef,P(-1))==48*(r**2-10),
    'quotient_derivative_at_minus_one': evaluate([qcoef[1],2*qcoef[2],3*qcoef[3]],P(-1))==-72*(r**2-10)-100*I*r,
    'cayley_denominator_cleared': sum((qcoef[k]*(1+I*z)**k*(1-I*z)**(3-k) for k in range(4)),P(0))==8*I*R,
    'cubic_discriminant': discr==-25*r**4*(120*r**4-3337*r**2+34200)-5269500*r**2-6480000,
    'inverse_cayley_pole': evaluate(Rcoef,-I)==-I*a,
    'quadratic_resultant': resultant==2177280+946944*r**2+I*(622080*r+241920*r**3),
    'positive_factor_discriminant': 3337**2-4*120*34200==-5280431,
    'exceptional_quadratic_discriminant': 20**2-4*25*15*10==-14600,
    'elimination_linear_combination': 70*(134136+32436*r**2-10404*r**4)+867*(-103032-40632*r**2+840*r**4)==-79939224-32957424*r**2,
}
assert all(checks.values()), checks
out={'arithmetic':'exact Gaussian integers in two formal variables','checks':checks,'status':'supplementary source-data diagnostics only; no Lean execution or mathematical acceptance claim'}
Path(__file__).with_name('exact_source_algebra.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

"""Independent referee checks; exact finite diagnostics, not a universal Lean proof."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib, json, subprocess, sys

root=Path(sys.argv[1]).resolve()
project=root/'eigenvalues-and-inverse-problems/SP-05/lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=json.loads((project/'reviews/statement-inputs.json').read_text())
for name,digest in spec['input_sha256'].items():
    assert sha((project/name).read_bytes())==digest,name
sources=json.loads((project/'reviews/initial/source-hashes.json').read_text())
for name,digest in sources['sha256'].items():
    data=(root/name).read_bytes()
    assert sha(data)==digest,name
    assert data==subprocess.check_output(['git','show',sources['source_base_commit']+':'+name],cwd=root),name
assert json.loads((root/'problem_ids.json').read_text())['SP-05']=='eigenvalues-and-inverse-problems/SP-05/README.md'
text=(root/'eigenvalues-and-inverse-problems/SP-05/solution.md').read_text().replace('\r\n','\n').replace('\r','\n')
block=text[text.index('## Theorem '):text.index('## Scope and review notes')].strip().encode()
assert len(block)==3483 and sha(block)==sources['historical_proof_block_sha256']
regenerated=subprocess.check_output([sys.executable,str(project/'reviews/initial/independent-exact-check.py'),str(root)])
assert regenerated==(project/'reviews/initial/independent-exact-check.json').read_bytes()

def tr(a):return [list(col) for col in zip(*a)]
def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def neg(a):return [[-x for x in row] for row in a]
def scale(a,k):return [[k*x for x in row] for row in a]
def vec(a):return [a[r][c] for c in range(len(a)) for r in range(len(a))]
def mv(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def kron(a,b):
    n=len(a)
    return [[a[c][d]*b[r][s] for d in range(n) for s in range(n)] for c in range(n) for r in range(n)]
checks=[]
for n in range(1,7):
    indices=[(c,r) for c in range(n) for r in range(n)]
    t=[[Q(i==j[::-1]) for j in indices] for i in indices]
    a=[[Q((i+2)*(j+3)-5*(i==j)) for j in range(n)] for i in range(n)]
    b=[[Q(3*i-2*j+1+(i==j)) for j in range(n)] for i in range(n)]
    x=[[Q((i+1)**2-3*j,1+i+j) for j in range(n)] for i in range(n)]
    assert mv(kron(a,b),vec(x))==vec(mul(mul(b,x),tr(a)))
    assert mv(t,vec(x))==vec(tr(x))
    assert dot(vec(x),vec(x))==sum(y*y for row in x for y in row)
    assert mul(mul(t,kron(a,b)),t)==kron(b,a)
    if n>=2:
        w=[[Q(1 if (i,j)==(0,1) else -1 if (i,j)==(1,0) else 0) for j in range(n)] for i in range(n)]
        assert tr(w)==neg(w) and mv(t,vec(w))==[-y for y in vec(w)]
        assert dot(vec(w),vec(w))==2
        for z in [vec(w),vec(add(x,tr(x)))]:
            assert dot(z,mv(add(kron(a,b),kron(b,a)),z))==2*dot(z,mv(kron(a,b),z))
    checks.append(n)

# Independently reconstruct every supplied n=2 arithmetic value.
a=[[Q(2),Q(1)],[Q(1),Q(2)]];b=[[Q(3),Q(0)],[Q(0),Q(1)]]
assert mul(a,b)!=mul(b,a)
assert a[0][0]==2 and a[0][0]*a[1][1]-a[0][1]*a[1][0]==3
assert b[0][0]==3 and b[0][0]*b[1][1]-b[0][1]*b[1][0]==3
expected=json.loads(regenerated)
assert [[str(y) for y in row] for row in kron(a,b)]==expected['actual_column_vec_kronecker']['K_A_tensor_B']
assert [[str(y) for y in row] for row in add(kron(a,b),kron(b,a))]==expected['actual_column_vec_kronecker']['J']
for x in [[[Q(0),Q(1)],[Q(1),Q(0)]],[[Q(0),Q(1)],[Q(-1),Q(0)]]]:
    assert dot(vec(x),mv(kron(a,b),vec(x)))/dot(vec(x),vec(x))==4
x=[[Q(-1),Q(0)],[Q(0),Q(2)]]
y=add(mul(a,x),mul(x,a));assert y==[[Q(-4),Q(1)],[Q(1),Q(8)]]

# Exact Gaussian rational arithmetic checks a genuinely complex Hermitian case.
class C:
    def __init__(self,r=0,i=0):self.r,self.i=Q(r),Q(i)
    @staticmethod
    def cast(z):return z if isinstance(z,C) else C(z)
    def __add__(self,z):z=C.cast(z);return C(self.r+z.r,self.i+z.i)
    __radd__=__add__
    def __neg__(self):return C(-self.r,-self.i)
    def __sub__(self,z):return self+-C.cast(z)
    def __mul__(self,z):z=C.cast(z);return C(self.r*z.r-self.i*z.i,self.r*z.i+self.i*z.r)
    __rmul__=__mul__
    def __eq__(self,z):z=C.cast(z);return (self.r,self.i)==(z.r,z.i)
    def conj(self):return C(self.r,-self.i)
def adj(a):return [[x.conj() for x in row] for row in tr(a)]
def inner(v,w):return sum(x.conj()*y for x,y in zip(v,w))
c=[[C(2),C(1,1)],[C(1,-1),C(3)]]
x=[[C(1),C(0,2)],[C(0,-2),C(1)]]
v=[C(1),C(0,1)]
assert c==adj(c) and x==adj(x)
assert c[0][0]==2 and c[0][0]*c[1][1]-c[0][1]*c[1][0]==4
assert mul(c,x)!=mul(x,c) and mv(x,v)==[-z for z in v]
y=add(mul(c,x),mul(x,c));assert y==adj(y)
assert inner(v,mv(c,v))==3
assert inner(v,mv(y,v))==-6 and inner(v,mv(y,v))==-2*inner(v,mv(c,v))

# Singular skew matrix in odd dimension: real modulus, equal Frobenius squares.
w=[[C(0),C(2),C(0)],[C(-2),C(0),C(0)],[C(0),C(0),C(0)]]
h=scale(w,C(0,1));absolute=[[C(2 if i==j and i<2 else 0) for j in range(3)] for i in range(3)]
assert h==adj(h) and mul(h,h)==mul(absolute,absolute)==mul(adj(w),w)
assert inner(vec(h),vec(h))==inner(vec(absolute),vec(absolute))==8
p=scale(add(absolute,h),Q(1,2));m=scale(add(absolute,neg(h)),Q(1,2))
assert mul(p,m)==[[C(0) for _ in range(3)] for _ in range(3)]
assert add(p,neg(m))==h and add(p,m)==absolute

config=json.loads((project/'comparator.json').read_text())
assert config['theorem_names']==['NLA.SP05.'+n for n in ['numerical_bound','column_vectorization','skew_witness','positive_minimizer','sector_minima','canonical_result']]
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert (project/'Solution.lean').read_text().strip()=='-- Statement preparation only; no proof implementation.\nimport NLA.SP05.Definitions'
assert len(list((project/'NLA').rglob('*.lean')))==1
assert (project/'Challenge.lean').read_text().count('  sorry')==6
out={'verdict':'PASS for exact finite diagnostics and source/hash preservation; no universal proof claimed','boundary_input_sha256':spec['input_sha256'],'source_sha256':sources['sha256'],'source_base_commit':sources['source_base_commit'],'historical_proof_block_sha256':sha(block),'historical_proof_block_bytes':len(block),'supplied_diagnostic_reproduced_byte_identically':True,'independent_conventions_dimensions':checks,'independent_n2_values_reconstructed':True,'complex_noncommuting_sylvester_identity':{'lambda':'-1','v_star_C_v':'3','v_star_Y_v':'-6'},'odd_singular_skew_modulus_frobenius_squared':'8','six_placeholders_only':True,'exact_comparator_six_names':True}
print(json.dumps(out,indent=2,sort_keys=True))

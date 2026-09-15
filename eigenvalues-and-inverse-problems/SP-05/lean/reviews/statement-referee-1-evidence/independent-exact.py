from fractions import Fraction as F
from pathlib import Path
import json

checks=[]
def check(n,c):
    assert c,n
    checks.append(n)
def mat(n,f):return [[f(i,j) for j in range(n)] for i in range(n)]
def tr(a):return list(map(list,zip(*a)))
def add(a,b):return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def neg(a):return [[-x for x in r] for r in a]
def mm(a,b):return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def mv(a,v):return [sum(x*y for x,y in zip(r,v)) for r in a]
def vec(a):return [a[i][j] for j in range(len(a)) for i in range(len(a))]
def unvec(v,n):return mat(n,lambda i,j:v[j*n+i])
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def kron(a,b):return [[a[i][j]*b[k][l] for j in range(len(a)) for l in range(len(b))] for i in range(len(a)) for k in range(len(b))]
def ident(n):return mat(n,lambda i,j:F(i==j))
def comm(n):
    inds=[(j,i) for j in range(n) for i in range(n)]
    return [[F(a==(b[1],b[0])) for b in inds] for a in inds]
def sqnorm(a):return sum(x*x for r in a for x in r)
def inv(a):
    n=len(a);t=[list(map(F,r))+ident(n)[i] for i,r in enumerate(a)]
    for i in range(n):
        k=next(k for k in range(i,n) if t[k][i]);t[k],t[i]=t[i],t[k]
        p=t[i][i];t[i]=[v/p for v in t[i]]
        for j in range(n):
            if i!=j:
                q=t[j][i];t[j]=[v-q*w for v,w in zip(t[j],t[i])]
    return [r[n:] for r in t]

for n in range(5):
    a=mat(n,lambda i,j:F((i+1)*(j+2)+(i==j)))
    b=mat(n,lambda i,j:F(2*i-3*j+1))
    t=comm(n);k=kron(a,b)
    check(f'n={n} T transpose',tr(t)==t)
    check(f'n={n} T involution',mm(t,t)==ident(n*n))
    check(f'n={n} tensor swap',mm(mm(t,k),t)==kron(b,a))
    for u in range(n):
        for v in range(n):
            x=mat(n,lambda i,j:F(i==u and j==v))
            check(f'n={n} matrix unit {(u,v)} column Kronecker',mv(k,vec(x))==vec(mm(mm(b,x),tr(a))))
            check(f'n={n} matrix unit {(u,v)} commutation',mv(t,vec(x))==vec(tr(x)))
            check(f'n={n} matrix unit {(u,v)} Frobenius denominator',dot(vec(x),vec(x))==sqnorm(x))
    for eps in [1,-1]:
        z=mat(n,lambda i,j:F(2*i+j+1));x=add(z,tr(z) if eps==1 else neg(tr(z)))
        v=vec(x)
        check(f'n={n} sector {eps} literal action',mv(t,v)==[eps*w for w in v])
        check(f'n={n} sector {eps} factor two',dot(v,mv(add(k,kron(b,a)),v))==2*dot(v,mv(k,v)))

for n in range(8):
    w=mat(n,lambda i,j:F(1 if (i,j)==(0,1) else -1 if (i,j)==(1,0) else 0))
    check(f'n={n} actual skew witness transpose',tr(w)==neg(w))
    check(f'n={n} witness squared norm boundary',sqnorm(w)==(2 if n>=2 else 0))
    check(f'n={n} skew nonempty iff valid dimension',any(x for r in w for x in r)==(n>=2))
check('closed certificate 0<2',F(0)<F(2))

# Independent noncommuting SPD sample (different from contributor's data).
a=[[F(2),F(2)],[F(2),F(5)]];b=[[F(7),F(2)],[F(2),F(5)]]
check('A positive leading minors',a[0][0]>0 and a[0][0]*a[1][1]-a[0][1]**2==6)
check('B positive leading minors',b[0][0]>0 and b[0][0]*b[1][1]-b[0][1]**2==31)
check('noncommuting inputs',mm(a,b)!=mm(b,a))
j=add(kron(a,b),kron(b,a));phi=inv(j)
check('true inverse both sides',mm(j,phi)==ident(4)==mm(phi,j))
check('real inverse self adjoint',tr(phi)==phi)
check('inverse commutes transpose',mm(phi,comm(2))==mm(comm(2),phi))

class G:
    def __init__(self,r=0,i=0):self.r=F(r);self.i=F(i)
    @staticmethod
    def cast(x):return x if isinstance(x,G) else G(x)
    def __add__(self,o):o=G.cast(o);return G(self.r+o.r,self.i+o.i)
    __radd__=__add__
    def __neg__(self):return G(-self.r,-self.i)
    def __sub__(self,o):return self+-G.cast(o)
    def __mul__(self,o):o=G.cast(o);return G(self.r*o.r-self.i*o.i,self.r*o.i+self.i*o.r)
    __rmul__=__mul__
    def __eq__(self,o):o=G.cast(o);return self.r==o.r and self.i==o.i
    def star(self):return G(self.r,-self.i)
    def __repr__(self):return f'({self.r})+({self.i})i'
def adj(a):return [[G.cast(x).star() for x in r] for r in tr(a)]
def trace(a):return sum(a[i][i] for i in range(len(a)))
def inner(a,b):return trace(mm(adj(a),b))
def cone2(a):
    return a==adj(a) and G.cast(a[0][0]).r>=0 and G.cast(a[1][1]).r>=0 and (a[0][0]*a[1][1]-a[0][1]*a[1][0]).r>=0

c=[[G(3),G(1,1)],[G(1,-1),G(2)]]
x=[[G(),G(0,1)],[G(0,-1),G()]];v=[G(1),G(0,1)]
y=add(mm(c,x),mm(x,c));quad=lambda m:dot([z.star() for z in v],mv(m,v))
check('complex C Hermitian positive definite',c==adj(c) and (c[0][0]*c[1][1]-c[0][1]*c[1][0])==G(4))
check('complex Hermitian negative eigenvector',x==adj(x) and mv(x,v)==[-z for z in v])
check('complex Sylvester exact contradiction identity',quad(y)==(-2)*quad(c)==G(-6))

h=[[G(),G(0,2)],[G(0,-2),G()]];mod=[[G(2),G()],[G(),G(2)]]
pos=[[G(1),G(0,1)],[G(0,-1),G(1)]];negpart=[[G(1),G(0,-1)],[G(0,1),G(1)]]
ph=lambda z:unvec(mv(phi,vec(z)),2)
check('complex PSD positive and negative parts',cone2(pos) and cone2(negpart))
check('parts difference and modulus sum',add(pos,neg(negpart))==h and add(pos,negpart)==mod)
check('orthogonal PSD parts',mm(pos,negpart)==mat(2,lambda i,j:G())==mm(negpart,pos))
check('actual inverse maps complex PSD sample to PSD',cone2(ph(negpart)))
cross=trace(mm(pos,ph(negpart)));gain=inner(mod,ph(mod))-inner(h,ph(h))
check('noncommuting cross trace positive',cross.i==0 and cross.r>0)
check('full Frobenius modulus comparison',gain==4*cross)
check('actual Frobenius norms equal',inner(mod,mod)==inner(h,h)==G(8))
check('real modulus square identity',mm(mod,mod)==mm(h,h))
for n in [1,2,3]:
    aa=mat(n,lambda i,j:F(2*(i==j)));bb=mat(n,lambda i,j:F(3*(i==j)))
    jj=add(kron(aa,bb),kron(bb,aa));check(f'n={n} repeated extremal eigenvalue sample',jj==mat(n*n,lambda i,j:F(12*(i==j))))

# Recompute the dossier's illustrative values as well as the separate sample.
source_a=[[F(2),F(1)],[F(1),F(2)]];source_b=[[F(3),F(0)],[F(0),F(1)]]
source_k=kron(source_a,source_b)
for sign in [1,-1]:
    vv=vec([[F(0),F(1)],[F(sign),F(0)]])
    check(f'dossier example sector value {sign} (not a minimum claim)',dot(vv,mv(source_k,vv))/dot(vv,vv)==4)
check('dossier leading principal minors',(source_a[0][0],source_a[0][0]*source_a[1][1]-source_a[0][1]**2)==(2,3) and (source_b[0][0],source_b[0][0]*source_b[1][1]-source_b[0][1]**2)==(3,3))
source_x=[[F(-1),F(0)],[F(0),F(2)]];source_y=add(mm(source_a,source_x),mm(source_x,source_a))
check('dossier real Sylvester sample',source_y==[[F(-4),F(1)],[F(1),F(8)]] and source_y[0][0]==-2*source_a[0][0]==-4)
h3=mat(3,lambda i,j:h[i][j] if i<2 and j<2 else G())
m3=mat(3,lambda i,j:mod[i][j] if i<2 and j<2 else G())
check('odd-dimensional singular Hermitian sample',h3==adj(h3) and all(h3[2][i]==0 for i in range(3)))
check('odd-dimensional real singular modulus',m3==adj(m3) and all(z.i==0 for row in m3 for z in row) and mm(m3,m3)==mm(h3,h3))
check('odd-dimensional Frobenius norm bridge',inner(h3,h3)==inner(m3,m3)==G(8))

record={'reviewer':'/root/reference_api_review (OpenAI GPT-6 Codex, independent AI)','phase':'independent pre-proof exact diagnostics, not universal proofs','result':'PASS','checks_count':len(checks),'checks':checks,'own_noncommuting_spd_sample':{'A':[[str(z) for z in r] for r in a],'B':[[str(z) for z in r] for r in b],'inverse':[[str(z) for z in r] for r in phi]},'complex_sylvester_value':str(quad(y)),'modulus_cross_term':str(cross),'modulus_quadratic_gain':str(gain),'contributor_checker_imported_or_executed':False}
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','checks':len(checks)}))

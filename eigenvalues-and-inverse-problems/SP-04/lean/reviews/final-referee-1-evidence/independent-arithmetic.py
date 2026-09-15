from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib, json

checks=[]
def check(name, condition):
    assert condition, name
    checks.append(name)
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def tr(a): return [list(row) for row in zip(*a)]
def diag(a): return [[x if i==j else F(0) for j in range(len(a))] for i,x in enumerate(a)]
def sub(a,b): return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def det(a):
    a=[list(map(F,row)) for row in a]; out=F(1)
    for i in range(len(a)):
        p=next((j for j in range(i,len(a)) if a[j][i]),None)
        if p is None:return F(0)
        if p!=i:a[p],a[i]=a[i],a[p];out=-out
        pivot=a[i][i];out*=pivot
        for j in range(i+1,len(a)):
            r=a[j][i]/pivot
            a[j]=[x-r*y for x,y in zip(a[j],a[i])]
    return out
def kron(a,b):
    return [[a[i][j]*b[k][l] for j in range(len(a[0])) for l in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]
def product_values(xs):
    out=F(1)
    for x in xs:out*=x
    return out
def f2(a):return sum(x*x for row in a for x in row)
def h(u,z):return det(sub(diag([z]*3),mm(tr(u),u)))

L=F(7,4); H=F(44,25); T=F(13,25)
check('exact discriminant endpoint',L*L-4*T==F(393,400))
check('first exported inequality',F(99,100)**2<L*L-4*T)
check('second exported inequality',F(275,198)<2)
check('third exported inequality',T*H*F(51,50)<1)
check('fourth exported inequality',F(201,400)<T)
check('source root-pattern product constant',T*H*F(51,50)==F(14586,15625))
check('source interval width',H-L==F(1,100))
check('difference quotient bound',F(88,25)/F(99,50)==F(16,9))
check('derivative-free large-root coefficient',(1+F(16,9))/2==F(25,18)==F(275,198))
check('large-root range bound',F(25,18)*(H-L)==F(1,72)<F(1,50))
check('T endpoint positive root exceeds 2',4-2*L-T==F(-1,50)<0)
check('T endpoint negative magnitude exceeds quarter',F(1,16)+H/4==F(201,400)<T)

sample=[F(v,1000) for v in [1751,1755,1759]]
lo=[F(v,1000) for v in [1750,1754,1758]]
hi=[F(v,1000) for v in [1752,1756,1760]]
check('all disjoint intervals within original box',L==lo[0]<hi[0]<lo[1]<hi[1]<lo[2]<hi[2]==H)
check('unchanged rational sample lies strictly inside intervals',all(a<x<b for a,x,b in zip(lo,sample,hi)))
gram_values=[h(diag(sample),z*z) for pair in zip(lo,hi) for z in pair]
nums=[-1937653044525,905786883351,648098176275,-649206984825,-910443880269,1954285183575]
for i,(v,n) in enumerate(zip(gram_values,nums)):
    check(f'Gram determinant endpoint {i}',v==F(n,10**18))
for i in range(3):check(f'opposite endpoint signs interval {i}',gram_values[2*i]*gram_values[2*i+1]<0)

# Separate exact stationary sample: a different t from the submitted checker.
t=F(2487,5000)
x=[-1/(F(2003,1000)*F(2007,1000)),F(2003,1000),F(2007,1000)]
s=[v-t/v for v in x]
check('independent exact stationary sample is admissible',L<s[0]<s[1]<s[2]<H)
check('independent multiplier inside strict selected range',0<t<T)
check('sample determinant negative one',product_values(x)==-1)
check('sample quadratic equations',all(v*v-a*v-t==0 for v,a in zip(x,s)))
y=[abs(x[0]),x[1],x[2]]
check('improving determinant positive one',product_values(y)==1)
gain=f2(sub(diag(s),diag(x)))-f2(sub(diag(s),diag(y)))
check('exact squared Frobenius gain',gain==4*s[0]*abs(x[0])>0)
check('full stationary matrix equation',mm(tr(diag(x)),sub(diag(s),diag(x)))==diag([-t]*3))

def companion(a,c):return [[a,-c],[F(1),F(0)]]
def K(ss,c):return kron(kron(companion(ss[0],c),companion(ss[1],c)),companion(ss[2],c))
v=[product_values(factors) for factors in product(*[[v,F(1)] for v in x])]
check('tensor vector has a nonzero last coordinate',v[-1]==1)
check('all companion eigenvector identities',all(mm(companion(a,-t),[[z],[F(1)]])==[[z*z],[z]] for a,z in zip(s,x)))
check('tensor eigenvector identity',mm(K(s,-t),[[z] for z in v])==[[-z] for z in v])
check('actual eliminant vanishes at stationary multiplier',det(sub(K(s,-t),diag([F(1)]*8)))*det(sub(K(s,-t),diag([F(-1)]*8)))==0)
for label,ss in [('original',sample),('independent',s)]:
    k0=K(ss,F(0)); prod_s=product_values(ss)
    check(label+' c=0 Kronecker matrix lower triangular',all(k0[i][j]==0 for i in range(8) for j in range(i+1,8)))
    check(label+' c=0 exact diagonal', [k0[i][i] for i in range(8)]==[prod_s]+[0]*7)
    r0=det(sub(k0,diag([F(1)]*8)))*det(sub(k0,diag([F(-1)]*8)))
    check(label+' nonzero eliminant evaluation',r0==1-prod_s*prod_s!=0)

# A rational, genuinely nondiagonal two-sided transport, with opposite orientations.
P=[[F(3,5),F(-4,5),F(0)],[F(4,5),F(3,5),F(0)],[F(0),F(0),F(1)]]
Q=[[F(0),F(1),F(0)],[F(1),F(0),F(0)],[F(0),F(0),F(1)]]
I=diag([F(1)]*3)
for name,a in [('P',P),('Q',Q)]:check(name+' both orthogonality equations',mm(tr(a),a)==I and mm(a,tr(a))==I)
check('both orthogonal determinant signs present',det(P)==1 and det(Q)==-1)
u=mm(mm(P,diag(s)),tr(Q)); xx=mm(mm(P,diag(x)),tr(Q)); yy=mm(mm(P,diag(y)),tr(Q))
check('transported selected determinant changes sign',det(xx)==1)
check('transported improved determinant changes sign',det(yy)==-1)
check('transport preserves full stationary equation',mm(tr(xx),sub(u,xx))==diag([-t]*3))
check('transport preserves both exact Frobenius distances',f2(sub(u,xx))==f2(sub(diag(s),diag(x))) and f2(sub(u,yy))==f2(sub(diag(s),diag(y))))
check('transport preserves strict improvement',f2(sub(u,yy))<f2(sub(u,xx)))
u0=mm(mm(P,diag(sample)),tr(Q))
check('full ambient nondiagonal sample satisfies polynomial signs',all(h(u0,a*a)*h(u0,b*b)<0 for a,b in zip(lo,hi)))

record={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent AI',
 'scope':'Independent exact diagnostics only; genericity, finiteness, uniqueness, and all-real inequalities require future Lean proofs.',
 'result':'PASS','checks_count':len(checks),'checks':checks,
 'gram_endpoint_values':[str(v) for v in gram_values],
 'independent_sample':{'t':str(t),'s':[str(v) for v in s],'x':[str(v) for v in x],'improvement':str(gain)},
 'source_checker_imported_or_executed':False}
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','checks':len(checks),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))

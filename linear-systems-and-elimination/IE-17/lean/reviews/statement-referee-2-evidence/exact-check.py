from fractions import Fraction as F
from pathlib import Path
import json

def T(a):return list(map(list,zip(*a)))
def M(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)]for row in a]
def V(a,x):return [sum(v*y for v,y in zip(row,x))for row in a]
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def normsq(x):return dot(x,x)
def sub(x,y):return [a-b for a,b in zip(x,y)]
def outer(x,y):return [[a*b for b in y]for a in x]
def ldl(a):
 n=len(a);L=[[F(i==j) for j in range(n)]for i in range(n)];d=[]
 assert a==T(a)
 for j in range(n):
  d.append(a[j][j]-sum(L[j][k]**2*d[k]for k in range(j)))
  assert d[j]>0
  for i in range(j+1,n): L[i][j]=(a[i][j]-sum(L[i][k]*L[j][k]*d[k]for k in range(j)))/d[j]
 assert M(M(L,[[d[i]if i==j else F(0)for j in range(n)]for i in range(n)]),T(L))==a
 minors=[];p=F(1)
 for di in d:p*=di;minors.append(p)
 return {'pivots':list(map(str,d)),'leading_minors':list(map(str,minors))}
A=[[F(v)for v in row]for row in [[1,0,0],[0,6,0],[0,0,5],[0,0,0]]];b=list(map(F,[11,1,1,1]));H=M(T(A),A);g=V(T(A),b)
x0=list(map(F,[0,0,0]));x1=[F(v,31201)for v in [11231,6126,5105]];x2=[F(v,55219)for v in [87659,7599,16865]];x3=[F(11),F(1,6),F(1,5)]
xs=[x0,x1,x2,x3];rs=[sub(b,V(A,x))for x in xs];qs=[V(T(A),r)for r in rs]
v2=V(H,g);v3=V(H,v2);generators=[g,v2,v3]
assert x1==[F(1021,31201)*v for v in g]
assert x2==[(F(16321)*v-F(383)*w)/110438 for v,w in zip(g,v2)]
assert x0==[0,0,0] and all(normsq(x)>0 for x in xs[1:])
assert all(normsq(q)>0 for q in qs[:3]) and qs[3]==[0,0,0]
assert rs[3]==[0,0,0,1]
iterates=[]
for k in [1,2,3]:
 basis=generators[:k];image=[V(H,u)for u in basis]
 assert all(dot(v,qs[k])==0 for v in image)
 gram=[[dot(u,v)for v in image]for u in image]
 iterates.append({'k':k,'normal_residual_squared':str(normsq(qs[k])),'Krylov_image_Gram':ldl(gram)})
assert rs[1]==[F(v,31201)for v in [331980,-5555,5676,31201]]
assert rs[2]==[F(v,55219)for v in [519750,9625,-29106,55219]]
C=M(A,T(A));w=list(map(F,[250,-1,1,27]));omega=normsq(w);kappa=F(1979,2000);cutoff=F(99,100)
def D_at(x,r):
 s=normsq(x);z=V(A,x);rr=normsq(r)
 return [[(rr*(i==j)-r[i]*r[j]+z[i]*z[j])/s for j in range(4)]for i in range(4)]
D1=D_at(x1,rs[1]);D2=D_at(x2,rs[2]);wcw=dot(w,V(C,w))/omega;wdw=dot(w,V(D1,w))/omega
assert wcw==F(62561,63231)<kappa and wdw==F(1642993919237,1713779258646)<kappa
s=normsq(x1);r=rs[1];z=V(A,x1);h=dot(w,z)
c0=sub(r,[dot(w,r)*v/omega for v in w]);a0=[-a+h*x/s for a,x in zip(V(T(A),w),x1)]
assert omega*s*kappa-h*h>0
first=M(outer(w,w),A)
E=[[-first[i][j]/omega+c0[i]*x1[j]/s+h*c0[i]*a0[j]/(omega*s*kappa-h*h)for j in range(3)]for i in range(4)]
ApE=[[A[i][j]+E[i][j]for j in range(3)]for i in range(4)]
assert V(T(ApE),sub(b,V(ApE,x1)))==[0,0,0]
EtE=M(T(E),E);upper=ldl([[kappa*(i==j)-EtE[i][j]for j in range(3)]for i in range(3)])
K=[[F(2407881992100)*(F(5,6)*C[i][j]+F(1,6)*D2[i][j]-cutoff*(i==j))for j in range(4)]for i in range(4)]
assert K==[[206417059721,-50293465200,1125984433750,-1435003762500],[-50293465200,83658415217471,206242965000,-26574143750],[1125984433750,206242965000,61800032332121,80360210700],[-1435003762500,-26574143750,80360210700,11170189945871]]
lower=ldl(K)
assert lower['leading_minors']==list(map(str,[206417059721,17265994657467102998545591,960941324740480331793743845178086291011,65442104145157248520714038046591467785805073713081]))
assert normsq(rs[2])/normsq(x2)>cutoff
approxs=[]
for x,r,q in zip(xs[1:3],rs[1:3],qs[1:3]):
 s=normsq(x);rr=normsq(r)
 approxs.append(sum(q[i]**2/(s*H[i][i]+rr)for i in range(3)))
assert approxs[0]==F(69694107852573439503892031925,69323394392991282508138323472)<F(503,500)
assert F(1007,1000)<approxs[1]==F(5430772101137459612205263871781350,5387955615790281743396033884265233)

# Independently reconstructed new auxiliary certificates from the numerical dossier.
assert normsq(x1)==F(189724262,973502401)
assert normsq(x2)==F(8026273307,3049137961)
assert normsq(x3)==F(108961,900)
assert normsq(rs[1])==F(111247297802,973502401)
assert normsq(rs[2])==F(274129000322,3049137961)
assert x3==[F(961,900)*u-F(31,450)*v+F(1,900)*w for u,v,w in zip(g,v2,v3)]
V3=T(generators)
detV3=sum(V3[0][j]*(V3[1][(j+1)%3]*V3[2][(j+2)%3]-V3[1][(j+2)%3]*V3[2][(j+1)%3])for j in range(3))
assert detV3==-3049200
assert h==F(2796519,31201)
assert omega*normsq(x1)*kappa-h*h==F(4049973517650519,973502401000)
dE=167211149523055806
BE=[[-165210014935131560,11610848662197240,2530244735132700],[39351326577989,-69867125644099962,-53313444486018375],[-21561235850426,71865739948107360,54839250040764540],[-18526767941430855,-75599190148266018,-58398875034268035]]
assert [[dE*v for v in row]for row in E]==BE
change=[[F(1),F(-18),F(23)],[F(0),F(1),F(0)],[F(0),F(0),F(1)]]
changeInv=[[F(1),F(18),F(-23)],[F(0),F(1),F(0)],[F(0),F(0),F(1)]]
assert M(change,changeInv)==[[F(i==j)for j in range(3)]for i in range(3)]
G=[[kappa*(i==j)-EtE[i][j]for j in range(3)]for i in range(3)]
dM=31584381671763314443807585554000
certM=[[32082903136661873741517122683,12090505500201922856789273706,-8382094473667110912199943291],[12090505500201922856789273706,2465624315241079991428765050975,31049384466533821447752395238],[-8382094473667110912199943291,31049384466533821447752395238,3427462740377387654443006689990]]
assert [[dM*z for z in row]for row in M(M(T(change),G),change)]==certM
assert certM==T(certM)
upperMargins=[certM[i][i]-sum(abs(certM[i][j])for j in range(3)if i!=j)for i in range(3)]
assert upperMargins==[11610303162792839972527905686,2422484425274344247124223382031,3388031261437186722083054351461]
assert all(t>0 for t in upperMargins)
weights=list(map(F,[10000,10,185,1287]));dK=F(2407881992100)
Kstar=[[K[i][j]-(dK/10000)*(i==j)for j in range(4)]for i in range(4)]
lowerMargins=[Kstar[i][i]*weights[i]-sum(abs(Kstar[i][j])*weights[j]for j in range(4)if i!=j)for i in range(4)]
assert lowerMargins==[F(6102817984650),F(2612912207614679,10),F(1352621546092623,20),F(1055456050659373,100)]
assert all(t>0 for t in lowerMargins)
assert normsq(rs[2])/normsq(x2)>F(9901,10000)>F(99,100)
record={'reviewer':'Codex AI agent /root/existing_verification_audit','method':'Independent Fraction arithmetic from explicit A,b, source formula and printed constants; no implementation/checker imports','result':'PASS','iterates':iterates,'krylov_basis_determinant':str(detV3),'terminal_residual':list(map(str,rs[3])),'first_error_feasible':True,'first_error_original_LDL':upper,'second_error_original_LDL':lower,'squared_approximations':list(map(str,approxs)),'upper_congruence':{'matrix_e_identity':True,'denominator':str(dM),'T_inverse_checked':True,'congruence_identity_checked':True,'positive_diagonal_margins':list(map(str,upperMargins))},'lower_weighted_certificate':{'weights':list(map(str,weights)),'positive_margins':list(map(str,lowerMargins)),'uniform_cutoff':'9901/10000','zero_new_residual_bound':str(normsq(rs[2])/normsq(x2))},'limitations':'Finite exact arithmetic and direct algebraic review only. No Lean mathematical proof, Comparator success or authoritative kernel verification claimed.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))

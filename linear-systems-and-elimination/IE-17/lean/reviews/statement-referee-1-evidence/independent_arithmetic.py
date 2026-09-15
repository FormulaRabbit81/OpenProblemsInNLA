#!/usr/bin/env python3
"""Independent IE-17 referee arithmetic; no repository checker imports.

OpenAI GPT-6 Codex /root/reference_api_review, 2026-09-15.
These exact rational checks are review evidence, not a Lean proof.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def tr(a):
    return [list(c) for c in zip(*a)]


def dot(x, y):
    return sum((a*b for a, b in zip(x, y)), F(0))


def mm(a, b):
    return [[dot(r, c) for c in tr(b)] for r in a]


def mv(a, x):
    return [dot(r, x) for r in a]


def add(a, b):
    return [[x+y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(c, a):
    return [[c*x for x in r] for r in a]


def outer(x, y):
    return [[a*b for b in y] for a in x]


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def diag(v):
    return [[x if i == j else F(0) for j in range(len(v))] for i, x in enumerate(v)]


def det(a):
    if len(a) == 1:
        return a[0][0]
    return sum(((-1)**j*a[0][j]*det([r[:j]+r[j+1:] for r in a[1:]])
                for j in range(len(a))), F(0))


def solve(a, b):
    rows=[list(row)+[rhs] for row, rhs in zip(a, b)]
    for k in range(len(b)):
        p=next(i for i in range(k, len(b)) if rows[i][k])
        rows[k], rows[p]=rows[p], rows[k]
        pivot=rows[k][k]
        rows[k]=[q/pivot for q in rows[k]]
        for i in range(len(b)):
            if i != k:
                coeff=rows[i][k]
                rows[i]=[q-coeff*r for q, r in zip(rows[i], rows[k])]
    return [r[-1] for r in rows]


checks=[]


def check(name, cond):
    if not cond:
        raise AssertionError(name)
    checks.append(name)


A=[[F(v) for v in row] for row in [[1,0,0],[0,6,0],[0,0,5],[0,0,0]]]
b=list(map(F, [11,1,1,1]))
H=mm(tr(A),A)
C=mm(A,tr(A))
g=mv(tr(A),b)
xs=[[F(11231,31201),F(6126,31201),F(5105,31201)],
    [F(87659,55219),F(7599,55219),F(16865,55219)],
    [F(11),F(1,6),F(1,5)]]
krylov_cols=[g, mv(H,g), mv(H,mv(H,g))]
gram_data=[]
for k in [1,2,3]:
    V=tr(krylov_cols[:k])
    HV=mm(H,V)
    gram=mm(tr(HV),HV)
    coeff=solve(gram,mv(tr(HV),g))
    x=mv(V,coeff)
    normal=[u-v for u,v in zip(g,mv(H,x))]
    check(f'Krylov solution k={k}',x==xs[k-1])
    check(f'normal equation k={k}',mv(tr(HV),normal)==[0]*k)
    check(f'Gram nonsingular k={k}',det(gram)>0)
    gram_data.append({'k':k,'gram':gram,'coeff':coeff,'det':det(gram)})
check('V3 determinant',det(tr(krylov_cols))==-3049200)
check('dossier Gram determinants',[d['det'] for d in gram_data]==[62402,96213585600,7531072718400000000])
check('dossier Krylov coefficients',[d['coeff'] for d in gram_data]==[[F(1021,31201)],[F(16321,110438),F(-383,110438)],[F(961,900),F(-31,450),F(1,900)]])
check('A full column rank',det(H)!=0)
zs=[mv(A,x) for x in xs]
rs=[[u-v for u,v in zip(b,z)] for z in zs]
ns=[mv(tr(A),r) for r in rs]
ss=[dot(x,x) for x in xs]
rhos=[dot(r,r) for r in rs]
check('dossier squared iterate norms',ss==[F(189724262,973502401),F(8026273307,3049137961),F(108961,900)])
check('dossier squared residual norms',rhos==[F(111247297802,973502401),F(274129000322,3049137961),F(1)])
check('exact termination',ns[2]==[0]*3 and ns[0]!=[0]*3 and ns[1]!=[0]*3 and g!=[0]*3)
check('nonzero compared and terminal iterates',all(s>0 for s in ss))
check('normal residual squares',list(map(lambda n:dot(n,n),ns))==[F(3593700,31201),F(5336100,55219),0])
check('normal residual decrease',dot(ns[0],ns[0])>dot(ns[1],ns[1])>0)
Ds=[scale(1/s,add(add(scale(rho,eye(4)),scale(-1,outer(r,r))),outer(z,z)))
    for s,rho,r,z in zip(ss,rhos,rs,zs)]

# Derive the perturbation from the original manuscript formula.
w=list(map(F,[250,-1,1,27])); omega=dot(w,w); kap=F(1979,2000)
x=xs[0]; r=rs[0]; z=zs[0]; s=ss[0]; h=dot(w,z)
c0=[v-t*dot(w,r)/omega for v,t in zip(r,w)]
a0=[-v+h*t/s for v,t in zip(mv(tr(A),w),x)]
den=omega*s*kap-h*h
E=add(add(scale(-1/omega,mm(outer(w,w),A)),scale(1/s,outer(c0,x))),scale(h/den,outer(c0,a0)))
dE=167211149523055806
BE=[[-165210014935131560,11610848662197240,2530244735132700],
    [39351326577989,-69867125644099962,-53313444486018375],
    [-21561235850426,71865739948107360,54839250040764540],
    [-18526767941430855,-75599190148266018,-58398875034268035]]
check('w norm square',omega==63231)
check('completion denominator',den==F(4049973517650519,973502401000)>0)
check('complete rational E',E==scale(F(1,dE),BE))
newA=add(A,E); newr=[u-v for u,v in zip(b,mv(newA,x))]
check('actual perturbed normal equations',mv(tr(newA),newr)==[0]*3)
check('source upper C value',dot(w,mv(C,w))/omega==F(62561,63231)<kap)
check('source upper D value',dot(w,mv(Ds[0],w))/omega==F(1642993919237,1713779258646)<kap)
G=add(scale(kap,eye(3)),scale(-1,mm(tr(E),E)))
check('original upper principal minors',[det([row[:j] for row in G[:j]]) for j in [1,2,3]]==[F(32082903136661873741517122683,31584381671763314443807585554000),F(4999825963008588746348642081657,63168763343526628887615171108000000),F(2511823903624540305487853,292667286279497105016000000000)])
T=[[F(v) for v in row] for row in [[1,-18,23],[0,1,0],[0,0,1]]]
M=[[32082903136661873741517122683,12090505500201922856789273706,-8382094473667110912199943291],
   [12090505500201922856789273706,2465624315241079991428765050975,31049384466533821447752395238],
   [-8382094473667110912199943291,31049384466533821447752395238,3427462740377387654443006689990]]
dM=31584381671763314443807585554000
check('unimodular T',det(T)==1)
check('upper congruence exact',mm(mm(tr(T),G),T)==scale(F(1,dM),M))
upper_margins=[M[i][i]-sum(abs(M[i][j]) for j in range(3) if i!=j) for i in range(3)]
check('new upper margins exact',upper_margins==[11610303162792839972527905686,2422484425274344247124223382031,3388031261437186722083054351461])
check('upper margins positive',all(v>0 for v in upper_margins))

# Reconstruct the source lower matrix before checking the NEW weighted certificate.
c=F(99,100); cp=F(9901,10000); dK=2407881992100
L=add(scale(F(5,6),C),scale(F(1,6),Ds[1]))
K=scale(dK,add(L,scale(-c,eye(4))))
expectedK=[[206417059721,-50293465200,1125984433750,-1435003762500],
           [-50293465200,83658415217471,206242965000,-26574143750],
           [1125984433750,206242965000,61800032332121,80360210700],
           [-1435003762500,-26574143750,80360210700,11170189945871]]
check('original lower K exact',K==expectedK)
check('original lower principal minors',[det([row[:j] for row in K[:j]]) for j in [1,2,3,4]]==[206417059721,17265994657467102998545591,960941324740480331793743845178086291011,65442104145157248520714038046591467785805073713081])
Kp=add(K,scale(F(-dK,10000),eye(4)))
check('uniform threshold shift exact',Kp==scale(dK,add(L,scale(-cp,eye(4)))))
v=list(map(F,[10000,10,185,1287]))
wm=[Kp[i][i]*v[i]-sum(abs(Kp[i][j])*v[j] for j in range(4) if i!=j) for i in range(4)]
check('new weighted margins exact',wm==[F(6102817984650),F(2612912207614679,10),F(1352621546092623,20),F(1055456050659373,100)])
check('new weighted margins positive',all(t>0 for t in wm))
W=mm(mm(diag(v),Kp),diag(v))
check('congruent weighted diagonal dominance',[W[i][i]-sum(abs(W[i][j]) for j in range(4) if i!=j) for i in range(4)]==[a*b for a,b in zip(v,wm)])
check('zero new residual ratio',rhos[1]/ss[1]==F(274129000322,8026273307)>cp>c)
check('exact error cutoff order',kap<c<cp)

# Independent coefficient expansion of the finite signed-square identity.
for label,S in [('upper',M),('lower',W)]:
    size=len(S)
    margins=[S[i][i]-sum(abs(S[i][j]) for j in range(size) if i!=j) for i in range(size)]
    rebuilt=diag(margins)
    for i in range(size):
        for j in range(i+1,size):
            t=abs(S[i][j]); sign=1 if S[i][j]>=0 else -1
            rebuilt[i][i]+=t; rebuilt[j][j]+=t
            rebuilt[i][j]+=sign*t; rebuilt[j][i]+=sign*t
    check(label+' sum-of-squares coefficient identity',rebuilt==S)

approx=[sum((n[i]*n[i]/(s*H[i][i]+rho) for i in range(3)),F(0))
        for n,s,rho in zip(ns,ss,rhos)]
check('approximation exact rational values',approx==[F(69694107852573439503892031925,69323394392991282508138323472),F(5430772101137459612205263871781350,5387955615790281743396033884265233),0])
check('approximation cutoff chain',approx[0]<F(503,500)<F(1007,1000)<approx[1])

def serial(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,list): return [serial(v) for v in x]
    if isinstance(x,dict): return {k:serial(v) for k,v in x.items()}
    return x

record=serial({'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review (independent AI)',
    'result':'PASS exact arithmetic only; not Lean proof', 'checks':checks,'checks_count':len(checks),
    'Gram_data':gram_data,'xs':xs,'residuals':rs,'normal_residuals':ns,'s':ss,'rho':rhos,
    'E':E,'upper_G':G,'upper_T':T,'upper_M':M,'upper_dM':dM,'upper_margins':upper_margins,
    'lower_K':K,'lower_Kstar':Kp,'lower_weights':v,'lower_weighted_margins':wm,
    'approximation_squares':approx})
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':record['result'],'checks_count':len(checks)}))

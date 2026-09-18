"""Exact rational Banach certificate for a D47 contact in an actual7-product chart.
All arithmetic used in the assertions is Gaussian integer or Fraction.
"""
from fractions import Fraction as F
import json,time
import lower_contact_certify as core
N=M=48;SCALE=10**70;INV_SCALE=10**60
core.N=N;core.M=M
G=core.G;z=G();one=G(1);add=core.add;scale=core.scale;conv=core.conv

def evaluate(theta,active):
 idx=0;am={k:j for j,k in enumerate(active)}
 def fixed(j):return core.poly(j),{},0
 def plus(a,b):
  av,ad,da=a;bv,bd,db=b;d=max(da,db);sa=SCALE**(d-da);sb=SCALE**(d-db)
  return add(scale(av,sa),scale(bv,sb)),{k:add(scale(ad.get(k,[z]*N),sa),scale(bd.get(k,[z]*N),sb)) for k in ad.keys()|bd.keys()},d
 def par():
  nonlocal idx
  p=[z]*N;p[0]=theta[idx];der={am[idx]:scale(core.poly(0),SCALE)} if idx in am else {};idx+=1;return p,der,1
 def lin(bs):
  nonlocal idx
  d=max(a[2] for a in bs)+1;v=[z]*N;der={}
  for bv,bd,dd in bs:
   sc=SCALE**(d-dd-1);t=theta[idx];v=add(v,scale([t*c for c in bv],sc))
   for k,dp in bd.items():der[k]=add(der.get(k,[z]*N),scale([t*c for c in dp],sc))
   if idx in am:
    k=am[idx];der[k]=add(der.get(k,[z]*N),scale(bv,sc*SCALE))
   idx+=1
  return v,der,d
 def mul(a,b):
  av,ad,da=a;bv,bd,db=b
  return conv(av,bv),{k:add(conv(ad.get(k,[z]*N),bv),conv(av,bd.get(k,[z]*N))) for k in ad.keys()|bd.keys()},da+db
 alpha,b,c,eta=[par() for _ in range(4)]
 Q=plus(fixed(4),mul(alpha,fixed(3)))
 R=plus(plus(mul(Q,Q),mul(b,mul(fixed(2),Q))),plus(mul(c,mul(fixed(1),Q)),mul(eta,fixed(3))))
 bs=[fixed(i) for i in range(3)]+[Q,R]
 for _ in range(4):
  top=bs[-1];low=bs[1:-1];P=mul(plus(top,lin(low)),plus(top,lin(low)));bs.append(P)
 val,der,d=lin(bs);assert idx==49 and d==33
 return val,[[der[j][i] for j in range(M)] for i in range(N)],SCALE**d

def hessian_bound(theta,active,radius):
 aset=set(active);idx=0
 def plus(a,b):return tuple(x+y for x,y in zip(a,b))
 def mul(a,b):
  v,u,h=a;w,t,k=b;return v*w,u*w+v*t,h*w+2*u*t+v*k
 def par():
  nonlocal idx
  free=idx in aset;a=(F(theta[idx].norm(),SCALE)+(radius if free else 0),F(int(free)),F(0));idx+=1;return a
 def lin(bs):
  out=(F(0),F(0),F(0))
  for b in bs:out=plus(out,mul(par(),b))
  return out
 fixed=(F(1),F(0),F(0));alpha,b,c,eta=[par() for _ in range(4)]
 Q=plus(fixed,mul(alpha,fixed));R=plus(plus(mul(Q,Q),mul(b,mul(fixed,Q))),plus(mul(c,mul(fixed,Q)),mul(eta,fixed)))
 bs=[fixed]*3+[Q,R]
 for _ in range(4):
  top=bs[-1];low=bs[1:-1];P=mul(plus(top,lin(low)),plus(top,lin(low)));bs.append(P)
 out=lin(bs);assert idx==49
 return out[2]

def main():
 start=time.monotonic();data=json.load(open(__file__.replace('certify.py','seed.json')));active=data['active_parameters']
 assert int(data['theta_denominator'])==SCALE and int(data['inverse_denominator'])==INV_SCALE
 theta=[G(r,i) for r,i in data['theta_numerators']];R=[[G(r,i) for r,i in row] for row in data['inverse_numerators']]
 val,J,den=evaluate(theta,active);val[47]=val[47]-G(den)
 print('exact circuit and Jacobian evaluated',time.monotonic()-start,flush=True)
 denom=den*INV_SCALE;res=[];defects=[]
 for i in range(N):
  s=z
  for k in range(N):s=s+R[i][k]*val[k]
  res.append(s.norm());row=0
  for j in range(N):
   s=z
   for k in range(N):s=s+R[i][k]*J[k][j]
   if i==j:s=s-G(denom)
   row+=s.norm()
  defects.append(row)
 eta=F(max(res),denom);defect=F(max(defects),denom);Rnorm=F(max(sum(x.norm() for x in row) for row in R),INV_SCALE)
 radius=F(1,10**45);H=hessian_bound(theta,active,radius);q=defect+Rnorm*H*radius
 print('eta',float(eta),'defect',float(defect),'Rnorm',float(Rnorm),'Hessian',float(H),'q',float(q),flush=True)
 assert eta<F(1,10**69) and defect<F(1,10**56)
 assert Rnorm<4000 and H<2*10**12 and q<F(1,10**28)
 assert q<F(1,2)
 assert eta+q*radius<radius
 # Stay inside the actual three-product chart b != 2, using the real part.
 assert abs(F(theta[1].r,SCALE)-2)>radius
 out={'status':'PASS','degree':47,'parameter_count':49,'active_parameters':active,'theta_denominator':str(SCALE),'inverse_denominator':str(INV_SCALE),'radius':str(radius),'preconditioned_residual_bound':str(eta),'inverse_defect_bound':str(defect),'inverse_norm_bound':str(Rnorm),'Hessian_bound':str(H),'contraction_bound':str(q),'self_map_bound':str(eta+q*radius),'b_real_distance_from_2':str(abs(F(theta[1].r,SCALE)-2)),'inequalities':['contraction_bound < 1/2','self_map_bound < radius','abs(Re(b)-2) > radius']}
 with open(__file__.replace('.py','.json'),'w') as f:json.dump(out,f,indent=2)
 print('PASS: exact rational D47 contact certificate',time.monotonic()-start,flush=True)
if __name__=='__main__':main()

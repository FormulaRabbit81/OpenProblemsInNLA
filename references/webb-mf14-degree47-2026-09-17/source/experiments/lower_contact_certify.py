"""Exact rational Banach certificate for a degree-45 contact point.
All certificate inequalities use integers/Fractions, never floats.
Floating output is human-readable diagnostic only. No external libraries.
"""
from fractions import Fraction as F
import json,time
N=46;M=46;SCALE=10**50;INV_SCALE=10**40
class G:
 __slots__=('r','i')
 def __init__(self,r=0,i=0):self.r=int(r);self.i=int(i)
 def __add__(a,b):return G(a.r+b.r,a.i+b.i)
 def __sub__(a,b):return G(a.r-b.r,a.i-b.i)
 def __mul__(a,b):return G(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r)
 def scale(a,k):return G(a.r*k,a.i*k)
 def norm(a):return abs(a.r)+abs(a.i)
 def __bool__(a):return bool(a.r or a.i)
z=G();one=G(1)
def poly(j):
 p=[z]*N;p[j]=one;return p

def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(a,k):return [x.scale(k) for x in a]
def conv(a,b):
 out=[z]*N;aa=[(i,x) for i,x in enumerate(a) if x];bb=[(j,y) for j,y in enumerate(b) if y]
 for i,x in aa:
  for j,y in bb:
   if i+j<N:out[i+j]=out[i+j]+x*y
 return out

def evaluate(theta,active):
 idx=0;active_map={k:j for j,k in enumerate(active)}
 def fixed(j):return poly(j),{},0
 def lin(bs):
  nonlocal idx
  deg=max(b[2] for b in bs)+1;v=[z]*N;der={}
  for bv,bd,d in bs:
   kscale=SCALE**(deg-d-1);t=theta[idx];v=add(v,scale([t*c for c in bv],kscale))
   for k,dv in bd.items():der[k]=add(der.get(k,[z]*N),scale([t*c for c in dv],kscale))
   if idx in active_map:
    k=active_map[idx];der[k]=add(der.get(k,[z]*N),scale(bv,kscale*SCALE))
   idx+=1
  return v,der,deg
 def mul(a,b):
  av,ad,da=a;bv,bd,db=b;ds={}
  for k in ad.keys()|bd.keys():ds[k]=add(conv(ad.get(k,[z]*N),bv),conv(av,bd.get(k,[z]*N)))
  return conv(av,bv),ds,da+db
 A=lin([fixed(i) for i in range(15)]);B=lin([fixed(i) for i in range(9)]);aa=mul(A,A)
 S=(add(aa[0],scale(B[0],SCALE)),{k:add(aa[1].get(k,[z]*N),scale(B[1].get(k,[z]*N),SCALE)) for k in aa[1].keys()|B[1].keys()},2)
 bs=[fixed(i) for i in range(5)]+[A,S]
 T=mul(lin(bs),lin(bs));bs.append(T);H=mul(lin(bs),lin(bs));bs.append(H)
 val,der,deg=lin(bs);assert idx==63 and deg==15
 return val,[[der[j][i] for j in range(M)] for i in range(N)],SCALE**deg

def hessian_bound(theta,active,radius):
 aset=set(active);idx=0
 def summ(a,b):return tuple(x+y for x,y in zip(a,b))
 def prod(a,b):
  v,u,h=a;w,t,k=b
  return v*w,u*w+v*t,h*w+2*u*t+v*k
 def lin(bs):
  nonlocal idx
  out=(F(0),F(0),F(0))
  for b in bs:
   free=idx in aset
   a=(F(theta[idx].norm(),SCALE)+(radius if free else 0),F(int(free)),F(0));idx+=1
   out=summ(out,prod(a,b))
  return out
 fixed=(F(1),F(0),F(0));A=lin([fixed]*15);B=lin([fixed]*9);S=summ(prod(A,A),B);bs=[fixed]*5+[A,S]
 T=prod(lin(bs),lin(bs));bs.append(T);H=prod(lin(bs),lin(bs));bs.append(H);out=lin(bs)
 assert idx==63
 return out[2]

def main():
 start=time.monotonic();path=__file__.replace('certify.py','seed.json');data=json.load(open(path));active=data['active_parameters']
 assert int(data['theta_denominator'])==SCALE and int(data['inverse_denominator'])==INV_SCALE
 theta=[G(r,i) for r,i in data['theta_numerators']]
 R=[[G(r,i) for r,i in row] for row in data['inverse_numerators']]
 val,J,den=evaluate(theta,active);val[45]=val[45]-G(den)
 print('exact circuit and Jacobian evaluated',time.monotonic()-start,flush=True)
 denom=den*INV_SCALE
 residual_pre=[];defect_rows=[]
 for i in range(N):
  s=z
  for k in range(N):s=s+R[i][k]*val[k]
  residual_pre.append(s.norm())
  row=0
  for j in range(N):
   s=z
   for k in range(N):s=s+R[i][k]*J[k][j]
   if i==j:s=s-G(denom)
   row+=s.norm()
  defect_rows.append(row)
 eta=F(max(residual_pre),denom);defect=F(max(defect_rows),denom);Rnorm=F(max(sum(x.norm() for x in row) for row in R),INV_SCALE)
 radius=F(1,10**25);Hbound=hessian_bound(theta,active,radius);q=defect+Rnorm*Hbound*radius
 print('eta',float(eta),'defect',float(defect),'Rnorm',float(Rnorm),'Hbound',float(Hbound),'q',float(q),flush=True)
 assert eta<F(1,10**49) and defect<F(1,10**35)
 assert Rnorm<4000 and Hbound<3*10**12 and q<F(1,10**8)
 assert q<F(1,2), 'Contraction fails'
 assert eta+q*radius<radius, 'Ball invariance fails'
 output={'status':'PASS','field':'Gaussian rationals','degree':45,'active_parameters':active,'theta_denominator':str(SCALE),'inverse_denominator':str(INV_SCALE),'theta_numerators':[[str(t.r),str(t.i)] for t in theta],'inverse_numerators':[[[str(t.r),str(t.i)] for t in row] for row in R],'radius':str(radius),'preconditioned_residual_bound':str(eta),'inverse_defect_bound':str(defect),'inverse_norm_bound':str(Rnorm),'Hessian_bound':str(Hbound),'contraction_bound':str(q),'self_map_bound':str(eta+q*radius),'inequalities':['contraction_bound < 1/2','self_map_bound < radius']}
 with open(__file__.replace('.py','.json'),'w') as f:json.dump(output,f,indent=2)
 print('PASS: exact rational contraction and self-map inequalities',time.monotonic()-start,flush=True)
if __name__=='__main__':main()

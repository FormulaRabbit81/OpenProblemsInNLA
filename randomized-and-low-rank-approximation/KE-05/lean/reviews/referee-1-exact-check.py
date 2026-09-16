from fractions import Fraction as F
import json
I=[[F(1),F(0)],[F(0),F(1)]]
def add(A,B):return [[A[i][j]+B[i][j] for j in range(2)] for i in range(2)]
def sm(c,A):return [[c*x for x in r] for r in A]
def sub(A,B):return add(A,sm(-1,B))
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def det(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def inv(A):return sm(1/det(A),[[A[1][1],-A[0][1]],[-A[1][0],A[0][0]]])
def diag(a,b):return [[F(a),F(0)],[F(0),F(b)]]
def trace(A):return A[0][0]+A[1][1]
O=[I,I,[[F(1),F(2)],[F(3),F(5)]]]
X=diag(1,2); P=mul(mul(inv(O[2]),diag(0,1)),O[2]);Q=mul(mul(sub(I,P),X),P)
k=trace(mul(sub(I,P),X));N=sm(-1/k,Q)
assert P==[[6,10],[-3,-5]] and Q==[[30,50],[-18,-30]] and k==7
assert det(N)==0 and sum(x*x for r in N for x in r)==F(68,7)**2
checks=[]
for e in [F(1,6),F(1,10),F(1,100)]:
 L=[diag(2,2),diag(e,2*e),diag(0,1)]
 for root in range(3):
  order=[root]+[i for i in range(3) if i!=root]
  B=[mul(mul(inv(O[j]),L[j]),O[j]) for j in order]
  hats=[None]*3;ss=[None]*3
  for i in reversed(range(3)):
   S=I
   for j in range(i+1,3):S=sub(mul(B[i],S),mul(S,hats[j]))
   oo=mul(O[order[i]],S)
   assert det(oo)!=0
   hats[i]=mul(mul(inv(oo),L[order[i]]),oo);ss[i]=S
  for i in range(3):
   S=I
   for j in range(i+1,3):S=sub(mul(B[i],S),mul(S,hats[j]))
   assert S==ss[i]
  if root==0:
   assert det(ss[1])==e*(2*e-k)
   assert det(ss[0])==2*(2-e)*(2-2*e)
   num=[[2*e*e-7*e+30,20*e+50],[3*e-18,4*e*e-14*e-30]]
   assert hats[1]==sm(1/(2*e-7),num)
  checks.append({'epsilon':str(e),'order':order,'determinants':[str(det(S)) for S in ss]})
for d in range(1,10):
 for k0 in range(d):
  order=[k0]+[i for i in range(d) if i!=k0]
  assert sorted(order)==list(range(d))
  for i in range(d):assert list(range(d))[i+1:][:d-1-i]==list(range(i+1,d))
print(json.dumps({'verdict':'PASS','P':P,'Q':Q,'kappa':k,'norm_squared':F(68,7)**2,'literal_recurrence_samples':checks,'limitation':'Exact finite diagnostics only; no probability, universal recurrence, or Lean proof claim.'},default=str,indent=2))

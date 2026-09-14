import json,itertools
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
p=Path(__file__).resolve().parent/'AC02_updated_research_pack'
def matrix(a):
 b=np.array(a,dtype=object);b=np.vectorize(Q)(b);return b.reshape(3,3) if b.ndim==1 else b
def rank(a):
 a=a.copy();r=0
 for j in range(a.shape[1]):
  hits=[i for i in range(r,len(a)) if a[i,j]]
  if not hits:continue
  k=hits[0];a[[r,k]]=a[[k,r]];a[r]=a[r]/a[r,j]
  for i in range(r+1,len(a)):a[i]-=a[i,j]*a[r]
  r+=1
 return r
for name in ['exact_five_blocks','exact_all_rank_two_five']:
 d=json.loads((p/'round2/data'/f'{name}.json').read_text())
 U,V,W,X,Y=([matrix(a) for a in d[k]] for k in ['U','V','W','X','Y'])
 for t in range(5):assert np.array_equal(W[t],X[t]@Y[t].T)
 for s in range(5):
  for t in range(5):assert np.array_equal(X[s].T@U[t]@V[s]@Y[t],np.eye(2,dtype=object) if s==t else np.zeros((2,2),dtype=object))
 ranks=[[rank(a) for a in f] for f in [U,V,W]]
 assert ranks==([[2]*5,[3,2,2,2,2],[2]*5] if name=='exact_five_blocks' else [[2]*5]*3)
 print(name,': 100 rational compatibility identities and factorizations PASS; ranks',ranks)
c=json.loads((p/'round2/certificates/sun_four_block_extension.json').read_text());d=json.loads((p/'round1/data/sun23.json').read_text())
factors=[]
for f in c['factorizations']:
 t=f['slot'];X=matrix(f['X']);Y=matrix(f['Y']);assert np.array_equal(matrix(d['W'][t]),X@Y.T);factors.append((X,matrix(d['V'][t])))
def minor(a,r,c):return a[r[0],c[0]]*a[r[1],c[1]]-a[r[0],c[1]]*a[r[1],c[0]]
# Every homogeneous quadratic is determined by evaluations on e_i and e_i+e_j.
points=[]
for i in range(9):
 v=[0]*9;v[i]=1;points.append(v)
 for j in range(i+1,9):
  v=[0]*9;v[i]=v[j]=1;points.append(v)
for v in points:
 U=np.array(v,dtype=object).reshape(3,3);F=np.vstack([X.T@U@V for X,V in factors])
 for rec in c['minor_identities']:
  a=minor(U,rec['target_rows'],rec['target_columns'])
  b=sum(Q(z['coefficient'])*minor(F,z['rows'],z['columns']) for z in rec['combination'])
  assert a==b
print('Sun extension: all nine homogeneous quadratic identities PASS on determining set of 45 points')

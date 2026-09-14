import numpy as np, json,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results'/'exploratory'
OUT.mkdir(parents=True,exist_ok=True)

def rankp(mat,p):
    A=mat.copy()%p; nr,nc=A.shape;r=0
    for c in range(nc):
        choices=np.flatnonzero(A[r:,c])
        if choices.size==0:continue
        a=r+int(choices[0]);A[[r,a]]=A[[a,r]]
        A[r,c:]=A[r,c:]*pow(int(A[r,c]),-1,p)%p
        if r+1<nr:
            A[r+1:,c:]=(A[r+1:,c:]-A[r+1:,c,None]*A[r:r+1,c:])%p
        r+=1
        if r==nr:break
    return r

def jac(n):
    V=np.array([[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]],dtype=np.int64)
    A=np.ones((1,1),dtype=np.int64)
    for _ in range(n): A=np.kron(A,V)
    d,r=A.shape
    J=np.zeros((d**3,3*d*r),dtype=np.int64)
    for mode in range(3):
        for i in range(d):
            for q in range(r):
                vs=[A[:,q]]*3;vs=list(vs);vs[mode]=np.eye(d,dtype=np.int64)[:,i]
                J[:,mode*d*r+i*r+q]=np.kron(np.kron(vs[0],vs[1]),vs[2])
    return J
out=[]
for n in [1,2]:
    J=jac(n)
    rec={'n':n,'shape':J.shape,'ranks':{}}
    for p in [101,103,107]:
        st=time.time();rank=rankp(J,p);rec['ranks'][p]=rank
        print(n,J.shape,p,rank,'nullity',J.shape[1]-rank,'sec',time.time()-st,flush=True)
    out.append(rec)
(OUT/'tangent_probe.json').write_text(json.dumps(out,indent=2))

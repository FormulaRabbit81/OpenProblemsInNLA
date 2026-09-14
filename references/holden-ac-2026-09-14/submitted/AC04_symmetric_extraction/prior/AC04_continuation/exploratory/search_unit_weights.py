"""Exploratory floating-point search; NEVER an exact certificate."""
import argparse, json, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results'/'exploratory'
OUT.mkdir(parents=True,exist_ok=True)
import numpy as np
import torch

def run(seed,iterations=500,noise=.05,lam=1.):
    torch.set_num_threads(1);torch.manual_seed(seed)
    dtype=torch.complex128
    V=torch.tensor([[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]],dtype=dtype)
    base=torch.kron(V,V); A0=base/3; B0=base/3; C0=base*9/16
    signs=torch.tensor([1,1,-1,-1],dtype=dtype); signs=torch.kron(signs,signs)
    B0=B0*signs[None,:]; C0=C0*signs[None,:]
    target=torch.einsum('ir,jr,kr->ijk',A0,B0,C0).detach()
    X,S,Y=torch.linalg.svd(A0@B0.T)
    U0=X[:,:3]*S[:3].sqrt(); V0=Y[:3,:].T*S[:3].sqrt()
    pars=[torch.nn.Parameter((z+noise*(torch.randn(z.shape,dtype=dtype))).contiguous()) for z in [A0,B0,C0,U0,V0]]
    logw=torch.nn.Parameter(torch.zeros(16,dtype=torch.float64));phase=torch.nn.Parameter(torch.zeros(16,dtype=torch.float64));pars.extend([logw,phase])
    def terms():
        A,B,C,U,W,l,p=pars
        A=A/torch.linalg.vector_norm(A,dim=0);B=B/torch.linalg.vector_norm(B,dim=0)
        weights=torch.exp(1j*p)
        weights=weights/torch.sqrt(weights.abs().square().mean())
        pred=torch.einsum('ir,jr,kr->ijk',A,B,C)
        M=(A*weights[None,:])@B.T
        terr=(pred-target).abs().square().sum()/36
        sv=torch.linalg.svdvals(M)
        cerr=sv[3:].square().sum()/sv.square().sum().clamp_min(1e-30)
        penalty=1e-10*C.abs().square().sum()
        return terr,cerr,penalty,(A,B,C,weights,M)
    opt=torch.optim.LBFGS(pars,lr=1,max_iter=iterations,tolerance_grad=1e-12,tolerance_change=1e-16,history_size=30,line_search_fn='strong_wolfe')
    calls=0
    def closure():
        nonlocal calls
        opt.zero_grad();t,c,p,_=terms();loss=t+lam*c+p;loss.backward();calls+=1;return loss
    st=time.time();opt.step(closure)
    with torch.no_grad():
        t,c,p,vals=terms();A,B,C,w,M=vals
        out={'seed':seed,'iterations_limit':iterations,'noise':noise,'lambda':lam,'calls':calls,'seconds':time.time()-st,
             'relative_tensor_error':float(t.sqrt()),'relative_contraction_tail':float(c.sqrt()),'contraction_singular_values':[float(z) for z in torch.linalg.svdvals(M)],'max_abs_C':float(C.abs().max()),'min_abs_weight':float(w.abs().min()),'max_abs_weight':float(w.abs().max()),'status':'EXPLORATORY_NOT_PROOF'}
        if float(t.sqrt())<1e-7 and float(c.sqrt())<1e-7:
            np.savez(OUT/f'candidate_{seed}.npz',**{k:v.numpy() for k,v in zip(['A','B','C','w'],[A,B,C,w])})
        return out
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--start',type=int,default=0);p.add_argument('--count',type=int,default=4);p.add_argument('--iterations',type=int,default=500);p.add_argument('--noise',type=float,default=.05);p.add_argument('--lam',type=float,default=1.)
    args=p.parse_args();results=[]
    for s in range(args.start,args.start+args.count):
        out=run(s,args.iterations,args.noise,args.lam);results.append(out);print(json.dumps(out),flush=True)
    (OUT/f'nonproduct_scan_{args.start}.json').write_text(json.dumps(results,indent=2))

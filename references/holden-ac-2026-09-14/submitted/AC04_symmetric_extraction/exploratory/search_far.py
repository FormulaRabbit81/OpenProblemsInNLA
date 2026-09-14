"""Non-certifying complex multistart search for a 16-term, rank-three-contraction formula.
Requires numpy and torch. Results cannot prove existence or nonexistence.
"""
import concurrent.futures as cf
import json, os, time
from pathlib import Path
os.environ['OMP_NUM_THREADS']='1'
os.environ['MKL_NUM_THREADS']='1'
ROOT=Path(__file__).resolve().parents[1]

def run(seed):
    import numpy as np
    import torch
    torch.set_num_threads(1)
    rng=np.random.default_rng(seed)
    V=np.array([[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]],dtype=complex)
    X=np.kron(V,V)
    target=np.einsum('ia,ja,ka->ijk',X,X,X)/16
    def rnd(shape): return (rng.normal(size=shape)+1j*rng.normal(size=shape))/2**0.5
    if seed%3==0:
        A=rnd((9,16)); B=rnd((9,16)); C=rnd((9,16))/10
        start='unstructured_random'
    else:
        scale=0.7 if seed%3==1 else 1.3
        R=np.exp(scale*rnd((4,2))); R=np.column_stack([R,1/(R[:,0]*R[:,1])])
        X=np.column_stack([np.kron(R[b]*V[:,a],V[:,b]) for a in range(4) for b in range(4)])
        norms=np.linalg.norm(X,axis=0)
        A=X/norms; B=X/norms; C=X*norms**2/16
        noise=0.2 if seed%3==1 else 0.6
        A+=noise*rnd((9,16));B+=noise*rnd((9,16));C+=noise*rnd((9,16))
        start='distant_adaptive_plus_noise'
    A=torch.tensor(A,dtype=torch.complex128,requires_grad=True)
    B=torch.tensor(B,dtype=torch.complex128,requires_grad=True)
    C=torch.tensor(C,dtype=torch.complex128,requires_grad=True)
    logs=torch.tensor(rng.normal(size=16),dtype=torch.float64,requires_grad=True)
    phases=torch.tensor(rng.uniform(-np.pi,np.pi,size=16),dtype=torch.float64,requires_grad=True)
    T=torch.tensor(target,dtype=torch.complex128)
    calls=0
    def measure():
        AA=A/torch.linalg.vector_norm(A,dim=0,keepdim=True)
        BB=B/torch.linalg.vector_norm(B,dim=0,keepdim=True)
        w=torch.exp(3*torch.tanh(logs)+1j*phases);w=w/torch.sqrt(torch.mean(abs(w)**2))
        err=torch.einsum('ia,ja,ka->ijk',AA,BB,C)-T
        er=(abs(err)**2).sum()/(abs(T)**2).sum()
        M=(AA*w)@BB.T
        sv=torch.linalg.svdvals(M)
        tail=(sv[3:]**2).sum()/(sv**2).sum()
        reg=1e-10*(abs(C)**2).sum()
        return er,tail,reg,sv,w,AA,BB
    opt=torch.optim.LBFGS([A,B,C,logs,phases],lr=0.6,max_iter=1000,history_size=35,
                           tolerance_grad=1e-11,tolerance_change=1e-15,line_search_fn='strong_wolfe')
    def closure():
        nonlocal calls
        opt.zero_grad(); er,tail,reg,*_=measure();loss=er+tail+reg
        loss.backward();calls+=1;return loss
    begin=time.monotonic()
    try:
        opt.step(closure)
        with torch.no_grad():
            er,tail,reg,sv,w,AA,BB=measure()
            out={'seed':seed,'start':start,'tensor_relative_residual':float(torch.sqrt(er)),
                 'contraction_relative_tail':float(torch.sqrt(tail)),
                 'singular_values':[float(x) for x in sv],
                 'minimum_weight_abs':float(abs(w).min()),'maximum_weight_abs':float(abs(w).max()),
                 'maximum_C_abs':float(abs(C).max()),'regularizer':float(reg),'calls':calls,
                 'elapsed_seconds':time.monotonic()-begin,'status':'EXPLORATORY_NOT_A_CERTIFICATE'}
            if float(er)<1e-12 and float(tail)<1e-12:
                np.savez(ROOT/'results'/f'candidate_{seed}.npz',A=AA.numpy(),B=BB.numpy(),C=C.numpy(),w=w.numpy())
            return out
    except Exception as exc:
        return {'seed':seed,'error':repr(exc),'calls':calls,'status':'SEARCH_ERROR'}

if __name__=='__main__':
    ROOT.joinpath('results').mkdir(exist_ok=True)
    results=[]
    with cf.ProcessPoolExecutor(max_workers=4) as pool:
        for out in pool.map(run,range(200,224)):
            results.append(out)
            print(json.dumps(out),flush=True)
            (ROOT/'results'/'far_search.json').write_text(json.dumps({'method':'bounded-weight complex L-BFGS, 1000 iterations per start','proof_status':'No inference of nonexistence is licensed by failure of this finite search.','runs':results},indent=2))

#!/usr/bin/env python3
"""Reproducible, UNRESTRICTED-coefficient rank-22 numerical experiments.

A nonzero residual proves nothing about tensor rank. Even a tiny residual is
not an exact certificate, and growing coefficients can signal a border-rank
sequence. All formerly zero entries are free in every least-squares update.
"""
from __future__ import annotations
import argparse
import json
from time import perf_counter
import numpy as np
from common import ROOT, tensor, load_scheme

def residual(f, t):
    return np.einsum('ta,tb,tc->abc',*f,optimize=True)-t

def balance(f):
    norms=np.linalg.norm(f,axis=2)
    if np.min(norms)<1e-100 or not np.all(np.isfinite(norms)):
        raise FloatingPointError('A factor collapsed or diverged.')
    geom=np.exp(np.mean(np.log(norms),axis=0))
    f *= (geom[None,:]/norms)[:,:,None]
    return f

def als(f, target, sweeps):
    f=balance(f.copy()); start=float(np.linalg.norm(residual(f,target)))
    trace=[]
    unfold=[np.moveaxis(target,g,0).reshape(9,81).T for g in range(3)]
    for it in range(sweeps):
        for g in range(3):
            other=[h for h in range(3) if h!=g]
            k=np.einsum('ti,tj->ijt',f[other[0]],f[other[1]]).reshape(81,22)
            f[g]=np.linalg.lstsq(k,unfold[g],rcond=1e-12)[0]
        balance(f)
        if it in (0,9,99,sweeps-1) or (it+1)%500==0:
            trace.append({'sweep':it+1,'residual_norm':float(np.linalg.norm(residual(f,target))),
                          'max_abs_coefficient':float(np.max(np.abs(f)))})
    return f,{'initial_residual_norm':start,'trace':trace,
              'final_residual_norm':float(np.linalg.norm(residual(f,target))),
              'max_abs_coefficient':float(np.max(np.abs(f)))}

def dense_jacobian(f):
    r=f.shape[1]; j=np.zeros((729,27*r),dtype=f.dtype)
    for g in range(3):
        for t in range(r):
            for k in range(9):
                fs=f[:,t,:].copy();fs[g]=0;fs[g,k]=1
                j[:,g*9*r+t*9+k]=np.einsum('a,b,c->abc',*fs).reshape(-1)
    return j

def polish(f,target,steps):
    """Damped holomorphic least-squares Gauss--Newton, works over C too."""
    f=balance(f.copy());lam=1e-3; history=[]
    for it in range(steps):
        res=residual(f,target).reshape(-1); norm=float(np.linalg.norm(res))
        j=dense_jacobian(f); gram=j.conj().T@j; rhs=-j.conj().T@res
        diag=np.maximum(np.real(np.diag(gram)),1e-3)
        accepted=False
        for trial in range(8):
            system=gram.copy();system.flat[::system.shape[0]+1]+=lam*diag
            try:step=np.linalg.solve(system,rhs).reshape(f.shape)
            except np.linalg.LinAlgError:lam*=10;continue
            cand=f+step;new=float(np.linalg.norm(residual(cand,target)))
            if np.isfinite(new) and new<norm:
                f=balance(cand);lam=max(lam/3,1e-12);accepted=True;break
            lam*=10
        history.append({'step':it+1,'residual_norm':float(np.linalg.norm(residual(f,target))),
                        'max_abs_coefficient':float(np.max(np.abs(f))),
                        'damping':lam,'accepted':accepted})
        if not accepted or history[-1]['residual_norm']<1e-12:break
    return f,history

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sweeps',type=int,default=500)
    parser.add_argument('--polish-steps',type=int,default=30)
    parser.add_argument('--random-starts',type=int,default=8)
    parser.add_argument('--seed',type=int,default=20260914)
    args=parser.parse_args()
    if min(args.sweeps,args.polish_steps,args.random_starts)<0:parser.error('Nonnegative counts required.')
    rng=np.random.default_rng(args.seed);t=tensor().astype(float); records=[]; finals=[]
    starts=[]
    for name in ('laderman23','sun23'):
        baseline=load_scheme(name).astype(float)
        for deleted in range(23):
            starts.append((f'{name}_delete_{deleted+1}',np.delete(baseline,deleted,axis=1)))
    for k in range(args.random_starts):
        f=rng.normal(size=(3,22,9))
        if k%2:f=f+1j*rng.normal(size=f.shape)
        starts.append((f'random_{k}',f/3))
    clock=perf_counter()
    for idx,(name,initial) in enumerate(starts):
        f,info=als(initial,t,args.sweeps)
        info.update({'name':name,'complex_coefficients':bool(np.iscomplexobj(initial))})
        records.append(info);finals.append(f)
        print(f'{idx+1}/{len(starts)} {name}: {info["final_residual_norm"]:.9g}',flush=True)
    order=sorted(range(len(finals)),key=lambda i:records[i]['final_residual_norm'])
    # Polish the four best starts and at least two genuinely complex starts.
    selected=order[:4]
    selected+= [i for i in order if records[i]['complex_coefficients'] and i not in selected][:2]
    for i in selected:
        f,hist=polish(finals[i],t,args.polish_steps);finals[i]=f
        records[i]['polishing']=hist
        records[i]['final_residual_norm']=float(np.linalg.norm(residual(f,t)))
        records[i]['max_abs_coefficient']=float(np.max(np.abs(f)))
        print('polished',records[i]['name'],records[i]['final_residual_norm'],flush=True)
    best=min(range(len(finals)),key=lambda i:records[i]['final_residual_norm'])
    np.savez_compressed(ROOT/'results'/'numerical_best_rank22.npz',factors=finals[best],target=t)
    out={'warning':'Numerical exploration only. Nonconvergence is NOT a lower bound. No exact rank-22 certificate.',
         'settings':vars(args),'all_coefficients_unrestricted':True,'starts':len(starts),
         'elapsed_seconds':perf_counter()-clock,'best_start':records[best]['name'],
         'best_residual_norm':records[best]['final_residual_norm'],
         'best_relative_residual':records[best]['final_residual_norm']/float(np.linalg.norm(t)),
         'records':records}
    (ROOT/'results'/'numerical_rank22_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Best residual',out['best_residual_norm'],'seconds',out['elapsed_seconds'])

if __name__=='__main__':main()

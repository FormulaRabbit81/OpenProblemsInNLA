#!/usr/bin/env python3
"""Replay exact certificates without importing the generator. No CAS or floats.

Requires NumPy. Run without Python's -O flag (assertions are proof checks).
The generator is not imported. Matrix integer arithmetic is deliberately
performed using object arrays where unbounded integer products are preferable.
"""
from __future__ import annotations
from collections import defaultdict
from itertools import product
import json
from math import isqrt
import numpy as np
from common import (ROOT, load_scheme, support_system, target, tensor, exponent,
                    jacobian, rank_mod, tangent_directions)

def read(name):
    return json.loads((ROOT/'proofs'/name).read_text())

def monomial_image(mon, e):
    return tuple(sum(int(e[i,j]) for i in mon) for j in range(e.shape[1]))

def check_forcing(name, f):
    cert = read(name+'_forcing.json')
    labels,polys = support_system(f)
    assert [list(lab) for lab in labels] == cert['labels']
    known = set()
    for step in cert['trace']:
        terms = polys[step['polynomial']]
        assert len(terms) == 2 and all(co != 0 for co,_ in terms)
        which = step['nonzero_term']; assert which in (0,1)
        assert all(i in known for i in terms[which][1])
        added = set(terms[1-which][1]) - known
        assert added == set(step['new_variables'])
        known.update(added)
    assert sorted(known) == cert['forced_variables']
    for g,t in product(range(3),range(23)):
        assert any(i in known and lab[:2] == (g,t) for i,lab in enumerate(labels))
    return {'allowed_variables':len(labels), 'forced_variables':len(known),
            'all_69_factor_vectors_nonzero':True, 'trace_steps':len(cert['trace'])}

def check_param(a, cert):
    a = np.array(a,dtype=object)
    rows,piv,free = cert['rows'],cert['pivots'],cert['free']
    n = a.shape[1]; r = len(piv)
    assert len(rows) == r and len(set(rows)) == r
    assert len(set(piv)) == r and sorted(piv+free) == list(range(n))
    inv = np.array(cert['inverse'],dtype=object)
    e = np.array(cert['E'],dtype=object)
    assert inv.shape == (r,r) and e.shape == (n,n-r)
    assert all(isinstance(x,int) for x in inv.flat)
    b = a[np.ix_(rows,piv)]
    assert np.array_equal(b@inv,np.eye(r,dtype=object))
    assert np.array_equal(inv@b,np.eye(r,dtype=object))
    assert np.array_equal(e[free,:],np.eye(n-r,dtype=object))
    assert np.array_equal(e[piv,:],-inv@a[np.ix_(rows,free)])
    assert not np.any(a@e)
    # Rank(A)=r: invertible minor gives >=r; n-r independent kernel columns
    # (identity on free coordinates) give <=r. Inverse is integral, so the
    # monomial equations have no unaccounted finite-root components.
    return e

def check_torus(f):
    cert = read('laderman_torus.json')
    labels,polys = support_system(f); n = len(labels)
    assert [list(lab) for lab in labels] == cert['labels']
    expected = [q for q,terms in enumerate(polys) if len(terms)==2]
    assert expected == cert['initial_relations'] and len(expected)==115
    a0=[]
    for q in expected:
        terms = polys[q]
        assert terms[0][0]+terms[1][0]==0
        a0.append([x-y for x,y in zip(exponent(terms[0][1],n),exponent(terms[1][1],n))])
    a0=np.array(a0,dtype=object)
    e0=check_param(a0,cert['initial'])
    assert e0.shape==(153,62)
    remaining=[q for q,terms in enumerate(polys) if len(terms)>2]
    assert remaining == [rec['polynomial'] for rec in cert['cancellations']]
    assert len(remaining)==4
    extra=[]
    for rec in cert['cancellations']:
        terms=polys[rec['polynomial']]
        i,j=rec['pair']; k=rec['survivor']
        assert len(terms)==4 and len({i,j,k})==3
        other=[q for q in range(4) if q not in (i,j,k)]
        assert len(other)==1 and terms[other[0]]==(-1,())
        assert terms[i][0]+terms[j][0]==0 and terms[k][0]==1
        delta=np.array([x-y for x,y in zip(exponent(terms[i][1],n),exponent(terms[j][1],n))],dtype=object)
        mult=np.array(rec['combination'],dtype=object)
        assert all(isinstance(x,int) for x in mult.flat)
        assert np.array_equal(mult@a0[cert['initial']['rows'],:],delta)
        extra.append(exponent(terms[k][1],n))
    a=np.vstack((a0,np.array(extra,dtype=object)))
    e=check_param(a,cert['final'])
    assert a.shape==(119,153) and e.shape==(153,58)
    assert all(abs(x)<=2 for x in e.flat)
    # All 729 identities are Laurent-polynomial identities: group exact
    # exponent vectors, then verify every coefficient vanishes.
    for terms in polys:
        result=defaultdict(int)
        for co,mon in terms:
            result[monomial_image(mon,e)]+=co
        assert all(v==0 for v in result.values())
    vmap={lab:i for i,lab in enumerate(labels)}
    signatures=[]
    for t in range(23):
        sig=defaultdict(int)
        for i,j,k in product(range(3),repeat=3):
            keys=[(0,t,3*i+j),(1,t,3*j+k),(2,t,3*i+k)]
            if all(key in vmap for key in keys):
                mon=tuple(vmap[key] for key in keys)
                co=int(f[keys[0]]*f[keys[1]]*f[keys[2]])
                sig[monomial_image(mon,e)]+=co
        sig={key:v for key,v in sig.items() if v}
        wanted=2 if t in (3,6,11,15) else 1
        assert sig=={(0,)*58:wanted}
        signatures.append(wanted)
    return labels,np.array(e,dtype=np.int64), {
        'initial_exponent_rank':91,'final_exponent_rank':95,
        'torus_dimension':58,'all_729_Laurent_identities':True,
        'signature':signatures,'integer_inverse_verified':True}

def check_gauge_slice(labels, e):
    cert=read('laderman_gauge_slice.json')
    torus=read('laderman_torus.json')
    b=np.zeros((153,55),dtype=object)
    for a,(g,t,k) in enumerate(labels):
        i,j=divmod(k,3)
        if g==0:
            b[a,t]=1; b[a,46+i]=1; b[a,49+j]=-1
        elif g==1:
            b[a,23+t]=1; b[a,49+i]=1; b[a,52+j]=-1
        else:
            b[a,t]=-1; b[a,23+t]=-1; b[a,46+i]=-1; b[a,52+j]=1
    d=b[torus['final']['free'],:]
    e=e.astype(object)
    assert np.array_equal(b,np.array(cert['gauge_exponents'],dtype=object))
    assert np.array_equal(d,np.array(cert['free_gauge_exponents'],dtype=object))
    assert np.array_equal(e@d,b)
    rows,cols=cert['selected_rows'],cert['selected_columns']
    assert len(set(rows))==len(set(cols))==52
    inv=np.array(cert['inverse'],dtype=object)
    assert all(isinstance(x,int) for x in inv.flat)
    q=d[np.ix_(rows,cols)]
    assert np.array_equal(q@inv,np.eye(52,dtype=object))
    assert np.array_equal(inv@q,np.eye(52,dtype=object))
    # Every gauge column is an integral combination of the selected ones.
    coeff=inv@d[rows,:]
    assert np.array_equal(d[:,cols]@coeff,d)
    extra=[i for i in range(58) if i not in rows]
    assert len(extra)==6 and extra==cert['slice_free_indices']
    assert np.array_equal(e[:,extra],np.array(cert['slice_E'],dtype=object))
    return {'effective_gauge_dimension':52,'slice_dimension':6,
            'unimodular_gauge_normalization':True,
            'slice_free_indices':extra}

def check_component(f, labels, e):
    cert=read('laderman_component.json'); p=cert['prime']
    assert p==1_000_003 and all(p%d for d in range(2,isqrt(p)+1))
    j=jacobian(f); h=tangent_directions(f,labels,e)
    assert h.shape==(621,76) and not np.any(j.astype(object)@h.astype(object))
    jr,jc=cert['jacobian_minor_rows'],cert['jacobian_minor_columns']
    hr,hc=cert['directions_minor_rows'],cert['directions_minor_columns']
    assert len(jr)==len(jc)==545 and len(set(jr))==len(set(jc))==545
    assert len(hr)==len(hc)==76 and len(set(hr))==len(set(hc))==76
    assert rank_mod(j[np.ix_(jr,jc)],p)[0]==545
    assert rank_mod(h[np.ix_(hr,hc)],p)[0]==76
    # Nonzero integer minors modulo p are nonzero over C. The 76 independent
    # exact kernel vectors then force rank(J)<=621-76, so equality holds.
    return {'jacobian_shape':[729,621], 'jacobian_rank_over_C':545,
            'independent_integral_kernel_directions':76,'JH_zero_over_Z':True,
            'prime':p,'component_dimension':76}

def small_rank(a):
    """Rational matrix rank by exact Fraction elimination (3x3 only)."""
    from fractions import Fraction
    b=[[Fraction(int(x)) for x in row] for row in a]
    r=0
    for c in range(len(b[0])):
        k=next((i for i in range(r,len(b)) if b[i][c]),None)
        if k is None: continue
        b[r],b[k]=b[k],b[r];p=b[r][c]
        b[r]=[v/p for v in b[r]]
        for i in range(r+1,len(b)):
            z=b[i][c];b[i]=[v-z*w for v,w in zip(b[i],b[r])]
        r+=1
        if r==len(b):break
    return r


def check_pairwise(name, f):
    forcing=read(name+'_forcing.json')
    known={tuple(forcing['labels'][i]) for i in forcing['forced_variables']}
    certs=read(name+'_pairwise.json')
    assert [c['modes'] for c in certs]==[[0,1],[1,2],[2,0]]
    for cert in certs:
        a,b=cert['modes']; remaining=set(range(23))
        assert len(cert['triangular_steps'])==23
        for row,t in cert['triangular_steps']:
            i,j=divmod(row,9)
            assert t in remaining and (a,t,i) in known and (b,t,j) in known
            assert f[a,t,i] and f[b,t,j]
            assert all(not(f[a,s,i] and f[b,s,j]) for s in remaining if s!=t)
            remaining.remove(t)
        assert not remaining
    return [23,23,23]

def check_tight_sun(f):
    cert=read('sun_tight.json'); qs=cert['output_ranks']
    assert len(qs)==23 and sum(qs)==27
    l=np.zeros((27,27),dtype=object);r=np.zeros((27,27),dtype=object)
    base=0;xs=[];ys=[]
    for t in range(23):
        x=np.array(cert['X'][t],dtype=object);y=np.array(cert['Y'][t],dtype=object)
        assert x.shape==y.shape==(3,qs[t])
        assert small_rank(x)==small_rank(y)==qs[t]
        assert np.array_equal(x@y.T, f[2,t].reshape(3,3))
        xs.append(x);ys.append(y)
        for i,j,k in product(range(3),repeat=3):
            for a in range(qs[t]):
                l[9*i+3*j+k,base+a]=int(f[0,t,3*i+j])*y[k,a]
                r[base+a,9*i+3*j+k]=x[i,a]*int(f[1,t,3*j+k])
        base+=qs[t]
    assert np.array_equal(l@r,np.eye(27,dtype=object))
    assert np.array_equal(r@l,np.eye(27,dtype=object))
    for s,t in product(range(23),repeat=2):
        block=xs[s].T @ f[0,t].reshape(3,3).astype(object) @ f[1,s].reshape(3,3).astype(object) @ ys[t]
        wanted=np.eye(qs[s],dtype=object) if s==t else np.zeros((qs[s],qs[t]),dtype=object)
        assert np.array_equal(block,wanted)
    return {'sum_output_ranks':27,'LR_and_RL_identity':True,'block_identities_verified':529,'output_ranks':qs}

def main():
    if not __debug__:
        raise RuntimeError('Do not run this proof checker with Python -O.')
    result={'global_exact_rank_determined':False,'certificate_status':'PASS'}
    for name in ('laderman23','sun23'):
        f=load_scheme(name)
        # Independent integer contraction with row-major target.
        for a,b,c in product(range(9),repeat=3):
            assert sum(int(f[0,t,a])*int(f[1,t,b])*int(f[2,t,c]) for t in range(23))==target(a,b,c)
        info=check_forcing(name,f)
        info['Brent_identities_verified']=729
        info['all_support_solutions_pairwise_Khatri_Rao_ranks']=check_pairwise(name,f)
        info['matrix_rank_sums']=[sum(small_rank(row.reshape(3,3)) for row in f[g]) for g in range(3)]
        result[name]=info
    f=load_scheme('laderman23');labels,e,info=check_torus(f)
    result['laderman_torus']=info
    result['laderman_gauge_slice']=check_gauge_slice(labels,e)
    result['laderman_component']=check_component(f,labels,e)
    result['sun_tight']=check_tight_sun(load_scheme('sun23'))
    text=json.dumps(result,indent=2)
    (ROOT/'results'/'exact_verification.json').write_text(text+'\n')
    print(text)

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Generate finite exact certificates. Verification is in verify.py.

Requires SymPy only during generation. All indexing is 0-based.
"""
from collections import defaultdict
import json
import numpy as np
import sympy as sp
from common import ROOT, PRIME, load_scheme, support_system, exponent, jacobian, rank_mod, tangent_directions

def dump(name, obj):
    (ROOT/'proofs'/name).write_text(json.dumps(obj, separators=(',',':'))+'\n')

def forcing_certificate(f):
    labels, polys = support_system(f)
    known = set(); trace = []
    while True:
        before = len(known)
        for q,terms in enumerate(polys):
            if len(terms) != 2:
                continue
            for which in range(2):
                if all(i in known for i in terms[which][1]):
                    added = sorted(set(terms[1-which][1]) - known)
                    if added:
                        trace.append({'polynomial':q, 'nonzero_term':which, 'new_variables':added})
                        known.update(added)
        if len(known) == before:
            break
    coverage = [[any(i in known and lab[:2] == (g,t) for i,lab in enumerate(labels))
                 for g in range(3)] for t in range(23)]
    return {'labels':labels, 'trace':trace, 'forced_variables':sorted(known),
            'all_factors_have_forced_nonzero':all(all(v) for v in coverage)}

def unit_pivots(a):
    """Integer elimination with +/-1 pivots; return a unimodular minor."""
    b = [list(map(int,a.row(i))) for i in range(a.rows)]
    rows = list(range(a.rows)); cols = list(range(a.cols)); r = 0
    for i in range(min(a.shape)):
        found = next(((j,k) for j in range(i,a.rows) for k in range(i,a.cols)
                      if abs(b[j][k]) == 1), None)
        if found is None:
            break
        j,k = found
        b[i],b[j] = b[j],b[i]; rows[i],rows[j] = rows[j],rows[i]
        for row in b:
            row[i],row[k] = row[k],row[i]
        cols[i],cols[k] = cols[k],cols[i]
        pivot = b[i][i]
        for j in range(i+1,a.rows):
            mult = b[j][i] // pivot
            if mult:
                b[j] = [x-mult*y for x,y in zip(b[j],b[i])]
        r += 1
    if any(b[j][k] for j in range(r,a.rows) for k in range(r,a.cols)):
        raise RuntimeError('Unit pivots did not exhaust rank.')
    return rows[:r],cols[:r]

def monomial_param(a):
    rows, piv = unit_pivots(a)
    free = [j for j in range(a.cols) if j not in piv]
    inv = a.extract(rows,piv).inv()
    if any(x.q != 1 for x in inv):
        raise RuntimeError('Nonintegral inverse: cannot assert a connected torus.')
    e = sp.zeros(a.cols,len(free))
    ep = -inv*a.extract(rows,free)
    for i,p in enumerate(piv): e[p,:] = ep[i,:]
    for i,q in enumerate(free): e[q,i] = 1
    assert a*e == sp.zeros(a.rows,len(free))
    return {'rows':rows,'pivots':piv,'free':free,
            'inverse':np.array(inv,dtype=np.int64).tolist(),
            'E':np.array(e,dtype=np.int64).tolist()}


def pairwise_certificates(f, forcing):
    known = {tuple(forcing['labels'][i]) for i in forcing['forced_variables']}
    certificates = []
    for a,b in ((0,1),(1,2),(2,0)):
        support = np.einsum('ta,tb->abt', f[a]!=0, f[b]!=0).reshape(81,23)
        remaining = set(range(23)); steps = []
        while remaining:
            found = None
            for row in range(81):
                live = [t for t in sorted(remaining) if support[row,t]]
                if len(live)==1 and (a,live[0],row//9) in known and (b,live[0],row%9) in known:
                    found = (row,live[0]); break
            assert found is not None
            steps.append(list(found)); remaining.remove(found[1])
        certificates.append({'modes':[a,b],'triangular_steps':steps})
    return certificates

def tight_sun_certificate(f):
    xs=[];ys=[];qs=[]
    for t in range(23):
        w=sp.Matrix(f[2,t].reshape(3,3))
        x,yt=w.rank_decomposition()
        assert all(z.q==1 for z in x) and all(z.q==1 for z in yt)
        xs.append(np.array(x,dtype=np.int64).tolist())
        ys.append(np.array(yt.T,dtype=np.int64).tolist())
        qs.append(x.cols)
    assert sum(qs)==27
    return {'X':xs,'Y':ys,'output_ranks':qs}

def gauge_slice_certificate(labels, final):
    """Split the fixed-support torus by term and diagonal basis rescalings."""
    b = sp.zeros(len(labels), 55)  # 46 slot gauges and 9 diagonal entries
    for a,(g,t,k) in enumerate(labels):
        i,j = divmod(k,3)
        if g == 0:
            b[a,t]=1; b[a,46+i]=1; b[a,49+j]=-1
        elif g == 1:
            b[a,23+t]=1; b[a,49+i]=1; b[a,52+j]=-1
        else:
            b[a,t]=-1; b[a,23+t]=-1; b[a,46+i]=-1; b[a,52+j]=1
    e = sp.Matrix(final['E']); d = b[final['free'],:]
    assert e*d == b
    cols = list(range(46))+[46,47,49,50,52,53]
    rows,_ = unit_pivots(d[:,cols])
    assert len(rows)==len(cols)==52
    inv = d.extract(rows,cols).inv()
    assert all(v.q==1 for v in inv)
    extra = [i for i in range(58) if i not in rows]
    return {'gauge_exponents':np.array(b,dtype=np.int64).tolist(),
            'free_gauge_exponents':np.array(d,dtype=np.int64).tolist(),
            'selected_rows':rows, 'selected_columns':cols,
            'inverse':np.array(inv,dtype=np.int64).tolist(),
            'slice_free_indices':extra,
            'slice_E':np.array(e[:,extra],dtype=np.int64).tolist()}

def main():
    for name in ('laderman23','sun23'):
        cert = forcing_certificate(load_scheme(name))
        assert cert['all_factors_have_forced_nonzero']
        dump(name+'_forcing.json', cert)
        dump(name+'_pairwise.json',pairwise_certificates(load_scheme(name),cert))
        print(name, 'forced',len(cert['forced_variables']),'of',len(cert['labels']))
    dump('sun_tight.json',tight_sun_certificate(load_scheme('sun23')))
    f = load_scheme('laderman23')
    labels,polys = support_system(f); n = len(labels)
    relations = []; origins = []
    for q,terms in enumerate(polys):
        if len(terms) != 2:
            continue
        assert terms[0][0] + terms[1][0] == 0
        relations.append([a-b for a,b in zip(exponent(terms[0][1],n),exponent(terms[1][1],n))])
        origins.append(q)
    a0 = sp.Matrix(relations); initial = monomial_param(a0)
    e0 = sp.Matrix(initial['E'])
    extra = []; cancellations = []
    for q,terms in enumerate(polys):
        if len(terms) <= 2:
            continue
        groups = defaultdict(list)
        for idx,(co,mon) in enumerate(terms):
            ex = sp.Matrix([exponent(mon,n)])
            
            if mon: groups[tuple(ex*e0)].append(idx)
        # Identify the cancelling pair of cubic monomials, leaving one cubic
        # and the constant -1. At z=1 all original cubic coefficients are +/-1.
        cancelled = [(i,j) for idxs in groups.values() for i in idxs for j in idxs
                     if i < j and terms[i][0]+terms[j][0] == 0]
        assert len(cancelled) >= 1
        pair = cancelled[0]
        remaining = [i for i in range(len(terms)) if i not in pair and terms[i][1]]
        assert len(remaining)==1 and terms[remaining[0]][0]==1
        survivor = remaining[0]
        delta = sp.Matrix([[a-b for a,b in zip(exponent(terms[pair[0]][1],n),exponent(terms[pair[1]][1],n))]])
        mult = delta[:,initial['pivots']] * sp.Matrix(initial['inverse'])
        assert mult*a0[initial['rows'],:] == delta
        assert all(x.q==1 for x in mult)
        cancellations.append({'polynomial':q,'pair':pair,'survivor':survivor,
                              'combination':list(map(int,mult))})
        extra.append(exponent(terms[survivor][1],n))
    a = a0.col_join(sp.Matrix(extra)); final = monomial_param(a)
    cert = {'labels':labels,'initial_relations':origins, 'initial':initial,
            'cancellations':cancellations,'final':final}
    dump('laderman_torus.json',cert)
    dump('laderman_gauge_slice.json',gauge_slice_certificate(labels,final))
    e = np.array(final['E'],dtype=np.int64)
    j = jacobian(f); h = tangent_directions(f,labels,e)
    assert np.max(np.abs(j@h))==0
    rj,ij,pj = rank_mod(j); rh,ih,ph = rank_mod(h)
    assert (rj,rh)==(545,76)
    dump('laderman_component.json', {'prime':PRIME,'jacobian_rank':rj,
         'jacobian_minor_rows':ij,'jacobian_minor_columns':pj,
         'directions_rank':rh,'directions_minor_rows':ih,'directions_minor_columns':ph})
    print('Torus dimensions',len(initial['free']),len(final['free']))
    print('Exact component certificates generated: J rank545, H rank76, JH=0.')

if __name__ == '__main__': main()

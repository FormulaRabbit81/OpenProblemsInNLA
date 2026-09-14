"""Exact certificates for non-coordinate P-lift retention.

Every computation here is over fractions.Fraction.  General, unbounded-size
claims are proved in the report; the code checks their finite algebraic seeds.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import permutations, product
from collections import defaultdict
from rational_linear import (matrix,zeros,eye,transpose,matmul,kron,blockdiag,
    inverse,rank,determinant,gram,paired,encode,decode,split_complement)

B1=matrix([[-1,0,-1],[0,-1,0],[-1,0,1]])
B2=matrix([[1,0,1],[0,-1,0],[1,0,-1]])
W1=matrix([['-1','-1','0','-1'],['-1/4','1/2','1/4','-1/4'],
           ['-1','0','-1','-1'],['1/2','-1/4','-1/4','0']])
W2=matrix([['-1','-1','0','0'],['-1/2','1/2','0','0'],
           ['-1','0','1','-1'],['1/4','0','-1/4','-1/4']])


def p_slices():
    ns=[zeros(3,3) for _ in range(3)]
    for i,j,k in permutations(range(3)):ns[k][i][j]=F(1)
    return ns


def tensor_terms(g):
    """Ordered sparse terms of C(g), with head coordinate zero."""
    out=defaultdict(F)
    for i,row in enumerate(g):
        for j,x in enumerate(row):
            if x:
                for key in [(0,i+1,j+1),(i+1,0,j+1),(i+1,j+1,0)]:out[key]+=x
    return {k:v for k,v in out.items() if v}


def make_core_certificate():
    return {'schema':'p-isotropic-slices-v1','B1':encode(B1),'B2':encode(B2),
            'slices':[encode(n) for n in p_slices()],
            'split_basis_1':encode(W1),'split_basis_2':encode(W2)}


def verify_core(data):
    if data.get('schema')!='p-isotropic-slices-v1':raise AssertionError('Wrong core schema')
    b1,b2=decode(data['B1']),decode(data['B2'])
    ns=[decode(a) for a in data['slices']]
    if ns!=p_slices():raise AssertionError('The slices do not describe P')
    if transpose(b1)!=b1 or transpose(b2)!=b2:raise AssertionError('Forms must be symmetric')
    if determinant(b1)!=2 or determinant(b2)!=2:raise AssertionError('Incorrect determinant')
    tensor_form=kron(b1,b2)
    rows=[[v for row in n for v in row] for n in ns]
    if rank(rows)!=3:raise AssertionError('The slice space is not three-dimensional')
    if gram(rows,tensor_form)!=zeros(3,3):raise AssertionError('Nonzero slice Gram matrix')
    for b,w in [(b1,decode(data['split_basis_1'])),(b2,decode(data['split_basis_2']))]:
        g=blockdiag(b,matrix([[2]]))
        if gram(w,g)!=paired(4):raise AssertionError('A rational split-basis check failed')
    return {'slice_dimension':3,'ambient_dimension':9,'zero_gram_entries':9,
            'determinants':['2','2'],'rational_split_bases_checked':2}


def forms_for_odd(l,b):
    if l<1 or l%2!=1:raise ValueError('A positive odd block size is required')
    j=blockdiag(paired(l-1),matrix([[1]])) if l>1 else matrix([[1]])
    return blockdiag(kron(b,j),matrix([[2]]))


def split_basis_for_odd(l,b,w4):
    """Rows giving a paired basis for (b tensor J_l) direct-sum [2]."""
    g=forms_for_odd(l,b);n=3*l+1;out=[];bi=inverse(b)
    for p in range(0,l-1,2):
        for a in range(3):
            e=[F(0)]*n;e[a*l+p]=1;out.append(e)
            f=[F(0)]*n
            for z in range(3):f[z*l+p+1]=bi[a][z]
            out.append(f)
    indices=[a*l+l-1 for a in range(3)]+[3*l]
    for wr in w4:
        rr=[F(0)]*n
        for k,i in enumerate(indices):rr[i]=wr[k]
        out.append(rr)
    if len(out)!=n:raise AssertionError('Wrong split basis dimension')
    return out


def retained_columns(l1,l2):
    """Sparse columns of the literal restriction C(G1) tensor C(G2) -> P tensor Z.

    Output rows: A_{a,i}, then B_{b,j}, then C_{c,i,j}.
    All coefficients are rational; no degeneration parameter is needed here.
    """
    g1=forms_for_odd(l1,B1);g2=forms_for_odd(l2,B2)
    t1,t2=len(g1),len(g2);n2=t2+1
    inv1=inverse(B1);inv2=inverse(B2)
    j1=blockdiag(paired(l1-1),matrix([[1]])) if l1>1 else matrix([[1]])
    j2=blockdiag(paired(l2-1),matrix([[1]])) if l2>1 else matrix([[1]])
    gi1=kron(inv1,j1);gi2=kron(inv2,j2)
    cols=defaultdict(list)
    na=3*l1;nb=3*l2
    for i,row in enumerate(gi1):
        for j,x in enumerate(row):
            if x:cols[(1+j)*n2].append((i,x))
    for i,row in enumerate(gi2):
        for j,x in enumerate(row):
            if x:cols[1+j].append((na+i,x))
    for a,b,c in permutations(range(3)):
        for i in range(l1):
            for j in range(l2):
                src=(1+a*l1+i)*n2+(1+b*l2+j)
                dst=na+nb+c*l1*l2+i*l2+j
                cols[src].append((dst,F(1)))
    return g1,g2,cols,na+nb+3*l1*l2


def expected_retention(l1,l2):
    na,nb=3*l1,3*l2;out=defaultdict(F)
    for a,b,c in permutations(range(3)):
        for i in range(l1):
            for j in range(l2):
                triple=(a*l1+i,na+b*l2+j,na+nb+c*l1*l2+i*l2+j)
                for key in permutations(triple):out[key]+=1
    return dict(out)


def verify_literal_retention(l1,l2):
    g1,g2,cols,dim=retained_columns(l1,l2);n2=len(g2)+1
    got=defaultdict(F);src1=tensor_terms(g1);src2=tensor_terms(g2)
    products_count=0
    for (i,j,k),x in src1.items():
        for (a,b,c),y in src2.items():
            arrays=[cols.get(i*n2+a,()),cols.get(j*n2+b,()),cols.get(k*n2+c,())]
            if not all(arrays):continue
            for (u,v1),(v,v2),(w,v3) in product(*arrays):
                got[(u,v,w)]+=x*y*v1*v2*v3;products_count+=1
    got={k:v for k,v in got.items() if v}
    expected=expected_retention(l1,l2)
    if got!=expected:raise AssertionError(f'Literal retained tensor failed for {l1},{l2}')
    if len(got)!=36*l1*l2:raise AssertionError('Unexpected support size')
    return {'left_block':l1,'right_block':l2,'target_dimension':dim,
            'target_nonzero_ordered_coefficients':len(got),
            'source_nonzero_terms':len(src1)*len(src2),
            'exact_scalar_products_accumulated':products_count}


def make_small_degeneration():
    """A literal 20 x 25 degeneration C4^2 -> P^2 direct-sum C10."""
    g1=blockdiag(B1,matrix([[2]]));g2=blockdiag(B2,matrix([[2]]))
    _,_,cols,dim=retained_columns(1,1)
    if dim!=9:raise AssertionError('Unexpected small retained dimension')
    u=zeros(9,25)
    for col,vals in cols.items():
        for row,x in vals:u[row][col]=x
    f=kron(g1,g2)
    basis=kron(W1,W2);seen=set();order=[]
    for i in range(16):
        if i in seen:continue
        a,b=divmod(i,4);mate=(a^1)*4+(b^1)
        order.extend([i,mate]);seen.update([i,mate])
    basis=[basis[i] for i in order]
    large=[(i+1)*5+(j+1) for i in range(4) for j in range(4)]
    isotropic=[[u[k][c] for c in large] for k in range(6,9)]
    comp=split_complement(f,isotropic,basis)
    head=[F(0)]*25;head[0]=1
    rows=u+[head]
    for rr in comp:
        row=[F(0)]*25
        for j,c in enumerate(large):row[c]=rr[j]
        rows.append(row)
    return {'schema':'literal-c4-square-p-square-c10-v1',
            'source_form_1':encode(g1),'source_form_2':encode(g2),
            'rows':encode(rows),'row_degrees':[0]*9+[-2]+[1]*10,
            'source_dimension':25,'target_dimension':20,
            'large_pairing_complement':encode(comp)}


def verify_small_degeneration(data):
    if data.get('schema')!='literal-c4-square-p-square-c10-v1':raise AssertionError('Wrong seed schema')
    g1,g2=decode(data['source_form_1']),decode(data['source_form_2'])
    if g1!=blockdiag(B1,matrix([[2]])) or g2!=blockdiag(B2,matrix([[2]])):
        raise AssertionError('Unexpected source forms')
    rows=decode(data['rows']);degs=data['row_degrees']
    if len(rows)!=20 or any(len(r)!=25 for r in rows):raise AssertionError('Bad map dimensions')
    if degs!=[0]*9+[-2]+[1]*10:raise AssertionError('Incorrect Laurent row degrees')
    if rank(rows)!=20:raise AssertionError('Target row map is not full rank')
    cols=defaultdict(list)
    for i,row in enumerate(rows):
        for j,x in enumerate(row):
            if x:cols[j].append((i,x))
    got=defaultdict(F)
    for (i,j,k),x in tensor_terms(g1).items():
        for (a,b,c),y in tensor_terms(g2).items():
            for (u,p),(v,q),(w,r) in product(cols[i*5+a],cols[j*5+b],cols[k*5+c]):
                got[(u,v,w)]+=x*y*p*q*r
    expected=expected_retention(1,1)
    for i in range(10):
        tr=(9,10+i,10+(i^1))
        # C10 has three head placements; the partner loop supplies the swaps.
        for key in [tr,(tr[1],tr[0],tr[2]),(tr[1],tr[2],tr[0])]:expected[key]=F(1)
    const={};positive=0
    for key,x in got.items():
        if not x:continue
        degree=sum(degs[i] for i in key)
        if degree<0:raise AssertionError(f'Uncancelled negative coefficient: {key}')
        if degree==0:const[key]=x
        else:positive+=1
    if const!=expected:raise AssertionError('The constant tensor is not P^2 direct-sum C10')
    large=[(i+1)*5+(j+1) for i in range(4) for j in range(4)]
    f=kron(g1,g2)
    c=[[rows[i][j] for j in large] for i in range(6,9)]
    v=[[rows[i][j] for j in large] for i in range(10,20)]
    if gram(c,f)!=zeros(3,3) or gram(c,f,v)!=zeros(3,10) or gram(v,f)!=paired(10):
        raise AssertionError('Small head isolation failed')
    if encode(v)!=data['large_pairing_complement']:raise AssertionError('Complement record differs')
    return {'source_dimension':25,'target_dimension':20,'all_ordered_coefficients_covered':8000,
            'constant_nonzero_coefficients':len(const),'positive_degree_nonzero_coefficients':positive,
            'uncancelled_negative_degree_coefficients':0,'active_main_dimension':3,
            'actual_main_dimension':9,'extracted_CW_size':10,'source_contraction_rank':rank(f)}

"""Exact cubic obstruction at the 2 x 4 x 2 grid plus its barycenter.

The 135-dimensional joint exterior kernel is certified by an integral basis,
checked over Q, and an independent modular rank bound. Necessary Segre and
Grassmann quadrics force the cubic contraction into a four-dimensional space
whose nonzero elements have first flattening rank at least nine. A contraction
of a decomposable (3,4,3) exterior tensor has first flattening rank at most three.
Thus the cubic tensor is zero. This is not an arbitrary-pole obstruction.
"""
from __future__ import annotations
from itertools import combinations,product
from functools import reduce
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import json
from exact import echelon,reduce_vector,kernel,add_scaled
from modular import rank as rank_mod,kernel as kernel_mod,check_relation

ROOT=Path(__file__).resolve().parents[1]
BASE=((0,1),(0,2,4,6),(0,8))
SPACES=((3,5,7,9,11,13,15),(3,5,7,10,11,12,13,14,15),(9,10,11,12,13,14,15))
AXES=(tuple(combinations(range(7),3)),tuple(combinations(range(9),4)),tuple(combinations(range(7),3)))
AXES_INV=tuple({v:i for i,v in enumerate(axis)} for axis in AXES)

def xor(values):
    return reduce(int.__xor__,values,0)

def joint_column(abc):
    vector={}
    for f,g in ((0,1),(0,2),(1,2)):
        h=3-f-g; I,J=AXES[f][abc[f]],AXES[g][abc[g]]
        for t,base in enumerate(BASE[h]):
            for i,ii in enumerate(I):
                for j,jj in enumerate(J):
                    if SPACES[f][ii]^SPACES[g][jj]^base==0:
                        labels=list(abc)
                        labels[f]=I[:i]+I[i+1:]
                        labels[g]=J[:j]+J[j+1:]
                        vector[f,g,t,tuple(labels)]=(-1)**(i+j)
    return vector

def cubic_column(abc):
    A,B,C=(AXES[f][abc[f]] for f in range(3));vector={}
    for a,b,c in product(range(3),range(4),range(3)):
        if SPACES[0][A[a]]^SPACES[1][B[b]]^SPACES[2][C[c]]==0:
            vector[A[:a]+A[a+1:],B[:b]+B[b+1:],C[:c]+C[c+1:]]=(-1)**(a+b+c)
    return vector

def modular_kernel_bound(prime=101):
    """Recompute rank of the full 154350-column joint map, blockwise."""
    AA,BB,CC=AXES;by=defaultdict(list)
    for ai,A in enumerate(AA):
        for bi,B in enumerate(BB):
            by[xor([SPACES[0][a] for a in A]+[SPACES[1][b] for b in B])].append((ai,bi))
    ab_kernel=[];ab_rank=0
    for charge,keys in sorted(by.items()):
        cols=[]
        for ai,bi in keys:
            A,B=AA[ai],BB[bi];v={}
            for t,c in enumerate(BASE[2]):
                for a,b in product(range(3),range(4)):
                    if SPACES[0][A[a]]^SPACES[1][B[b]]^c==0:
                        v[t,A[:a]+A[a+1:],B[:b]+B[b+1:]]=(-1)**(a+b)
            cols.append(v)
        rank,rels=kernel_mod(cols,prime);ab_rank+=rank
        for rel in rels:
            check_relation(cols,rel,prime)
            ab_kernel.append((charge,{keys[i]:v for i,v in rel.items()}))
    assert ab_rank+len(ab_kernel)==4410
    by=defaultdict(list)
    for charge,rel in ab_kernel:
        for ci,C in enumerate(CC):
            by[charge^xor(SPACES[2][c] for c in C)].append((rel,ci))
    cache={};records=[]
    for charge,keys in sorted(by.items()):
        cols=[]
        for rel,ci in keys:
            v={}
            for (ai,bi),coef in rel.items():
                abc=ai,bi,ci
                if abc not in cache:
                    cache[abc]={row:c for row,c in joint_column(abc).items() if row[:2]!=(0,1)}
                for row,c in cache[abc].items():
                    v[row]=(v.get(row,0)+coef*c)%prime
            cols.append({k:c for k,c in v.items() if c})
        cols.sort(key=len)
        rank,_=rank_mod(cols,prime)
        records.append({'charge':charge,'domain_dimension':len(cols),'rank':rank})
    full_rank=ab_rank*35+sum(r['rank'] for r in records)
    assert full_rank==154350-135
    return {'prime':prime,'full_domain_dimension':154350,'rank_mod_prime':full_rank,
            'kernel_dimension_mod_prime':135,'AB_rank':ab_rank,'remaining_blocks':records}

def addproduct(poly,left,right,scale=1):
    for i,a in left.items():
        for j,b in right.items():
            key=min(i,j),max(i,j)
            poly[key]=poly.get(key,F(0))+scale*a*b

def cleaned(poly):
    return {k:c for k,c in poly.items() if c}

def quadrics(coords,descriptions):
    result=[]
    for rec in descriptions:
        kind,f=rec[:2];poly={}
        if kind=='Segre':
            a,b=map(tuple,rec[2:]);aa,bb=list(a),list(b)
            aa[f],bb[f]=b[f],a[f]
            addproduct(poly,coords.get(a,{}),coords.get(b,{}))
            addproduct(poly,coords.get(tuple(aa),{}),coords.get(tuple(bb),{}),-1)
        else:
            assert kind=='Plucker'
            fixed,I,J=rec[2:];I,J=tuple(I),tuple(J)
            for pos,j in enumerate(J):
                if j in I:continue
                seq=I+(j,)
                sign=(-1)**sum(seq[a]>seq[b] for a in range(len(seq)) for b in range(a+1,len(seq)))
                li=AXES_INV[f][tuple(sorted(seq))];ri=AXES_INV[f][J[:pos]+J[pos+1:]]
                a,b=list(fixed),list(fixed);a.insert(f,li);b.insert(f,ri)
                addproduct(poly,coords.get(tuple(a),{}),coords.get(tuple(b),{}),(-1)**pos*sign)
        result.append(cleaned(poly))
    return result

def restrict_polys(polys,columns,original_dim):
    coordinates=[{j:v.get(i,0) for j,v in enumerate(columns) if v.get(i,0)} for i in range(original_dim)]
    result=[]
    for poly in polys:
        dest={}
        for (a,b),c in poly.items():addproduct(dest,coordinates[a],coordinates[b],c)
        result.append(cleaned(dest))
    return result

def restrict_parameters(columns,linear_forms):
    constraints=[{j:form.get(i,0) for j,form in enumerate(linear_forms) if form.get(i,0)} for i in range(len(columns))]
    allowed=kernel(constraints);result=[]
    for a in allowed:
        v={}
        for j,c in a.items():add_scaled(v,columns[j],c)
        result.append(v)
    return result

def verify():
    for i in range(3):
        products={xor(v) for v in product(*(BASE[j] for j in range(3) if j!=i))}
        actual=tuple(x for x in range(16) if x not in BASE[i] and x not in products)
        assert actual==SPACES[i]
    raw=json.loads((ROOT/'certificates/grid_joint_kernel.json').read_text())['basis']
    K=[{tuple(row[:3]):F(row[3]) for row in rel} for rel in raw]
    assert len(K)==len(echelon(K))==135
    cache={}
    for vector in K:
        image={}
        for abc,c in vector.items():
            if abc not in cache:cache[abc]=joint_column(abc)
            add_scaled(image,cache[abc],c)
        assert not image
    modular=modular_kernel_bound()
    # A characteristic-zero kernel has dimension <= the modular kernel;
    # 135 independent rational kernel vectors establish equality.
    coords=defaultdict(dict)
    for j,v in enumerate(K):
        for abc,c in v.items():coords[abc][j]=c
    squares=json.loads((ROOT/'certificates/grid_square_relations.json').read_text())
    eliminated=set();square_counts=[]
    for batch in squares['rounds']:
        for rec in batch:
            poly={}
            for a,b,c in [(rec['left'],rec['right'],1),(rec['cross_left'],rec['cross_right'],-1)]:
                left={j:x for j,x in coords.get(tuple(a),{}).items() if j not in eliminated}
                right={j:x for j,x in coords.get(tuple(b),{}).items() if j not in eliminated}
                addproduct(poly,left,right,c)
            poly=cleaned(poly);v=rec['variable']
            assert len(poly)==1 and (v,v) in poly
            f=rec['factor'];a,b=list(rec['left']),list(rec['right']);a[f],b[f]=b[f],a[f]
            assert a==rec['cross_left'] and b==rec['cross_right']
        eliminated.update(rec['variable'] for rec in batch)
        square_counts.append(len(batch))
    remaining=squares['remaining'];assert set(remaining)==set(range(135))-eliminated
    assert len(remaining)==48
    at={j:i for i,j in enumerate(remaining)}
    coords={abc:{at[j]:x for j,x in v.items() if j in at} for abc,v in coords.items()}
    descriptions=json.loads((ROOT/'certificates/grid_quadratic_relations.json').read_text())['selected_relations']
    polys=quadrics(coords,descriptions);piv=echelon(polys)
    assert len(piv)==1143
    # L*x_j belongs to the quadratic ideal for every j. Therefore L^2 does,
    # and L vanishes at every complex solution. No finite-field inference.
    columns=[]
    for i in range(48):
        v={}
        for j in range(48):
            rem=reduce_vector({(min(i,j),max(i,j)):F(1)},piv)
            v.update({(j,key):c for key,c in rem.items()})
        columns.append(v)
    socle=kernel(columns);assert len(socle)==17
    transform=restrict_parameters([{i:F(1)} for i in range(48)],socle)
    assert len(transform)==31
    cubic_cache={};cubiccols=[]
    for index in remaining:
        image={}
        for abc,c in K[index].items():
            if abc not in cubic_cache:cubic_cache[abc]=cubic_column(abc)
            add_scaled(image,cubic_cache[abc],c)
        cubiccols.append(image)
    def contraction(columns):
        images=[]
        for col in columns:
            image={}
            for j,c in col.items():add_scaled(image,cubiccols[j],c)
            images.append(image)
        return images
    images=contraction(transform);rows=defaultdict(dict)
    for j,image in enumerate(images):
        for key,c in image.items():rows[key][j]=c
    row_basis=list(echelon(rows.values()).values());assert len(row_basis)==7
    piv=echelon(restrict_polys(polys,transform,48));assert len(piv)==463
    kill=[]
    for linear in row_basis:
        square={};addproduct(square,linear,linear)
        if not reduce_vector(cleaned(square),piv):kill.append(linear)
    assert len(kill)==3
    transform=restrict_parameters(transform,kill);assert len(transform)==28
    images=contraction(transform);image_basis=list(echelon(images).values())
    assert len(image_basis)==4
    # For each of four coordinates in the cubic-image basis, find columns
    # in the A flattening that occur in no other basis tensor. Those columns
    # give rank >= 9 whenever that coefficient is nonzero. For a genuine
    # decomposable exterior tensor the first flattening rank is <= 3.
    supports=[{key[1:] for key in image} for image in image_basis]
    ranks=[]
    for i,image in enumerate(image_basis):
        exclusive=supports[i]-set().union(*(supports[j] for j in range(4) if j!=i))
        cols=[{key[0]:c for key,c in image.items() if key[1:]==column} for column in sorted(exclusive)]
        rank=len(echelon(cols));assert rank==9
        ranks.append({'basis_index':i,'exclusive_column_count':len(exclusive),'exclusive_column_rank':rank})
    return {'status':'PASS','base_characters':BASE,'normal_spaces':SPACES,
            'modular_kernel_bound':modular,'rational_kernel_dimension':135,
            'all_135_rational_kernel_vectors_independently_checked':True,
            'square_elimination_counts':square_counts,'remaining_after_squares':48,
            'necessary_quadratic_span_rank':1143,'linear_socle_dimension':17,
            'parameter_dimension_after_socle':31,'cubic_coefficient_rank_before_extra_squares':7,
            'additional_square_forms':3,'remaining_parameter_dimension':28,
            'final_cubic_image_dimension':4,'exclusive_column_rank_certificates':ranks,
            'conclusion':'Every admissible (3,4,3) normal-subspace triple at this grid configuration has zero cubic tensor.',
            'scope':'Grid-plus-barycenter limiting configuration, normalized holomorphic factor curves and scalar poles at most three. Not all configurations or higher poles.'}

if __name__=='__main__':
    result=verify()
    (ROOT/'results/grid_obstruction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

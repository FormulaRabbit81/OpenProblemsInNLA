"""Independent exact reconstruction of AC02/AC03 supported scopes.

Does not import submitted checker code. Read submitted rational data only.
"""
from pathlib import Path
from itertools import product, combinations
from collections import defaultdict, Counter
import json
import argparse
import sympy as s

parser=argparse.ArgumentParser()
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--out',type=Path,required=True)
args=parser.parse_args()
base=args.repo/'references/holden-ac-2026-09-14/submitted'
out=args.out
out.mkdir(parents=True,exist_ok=True)
p=base/'AC02_updated_research_pack'
def mat(v):
    return s.Matrix([[s.Rational(x) for x in row] for row in v]) if isinstance(v[0],list) else s.Matrix(3,3,[s.Rational(x) for x in v])
def read(rel):return json.loads((p/rel).read_text())
report={}

def check_coefficients(data):
    arrays={k:[[s.Rational(x) for x in row] for row in data[k]] for k in ('U','V','W')}
    bad=0
    for i,j,k,l,m,n in product(range(3),repeat=6):
        val=sum(arrays['U'][t][3*i+j]*arrays['V'][t][3*k+l]*arrays['W'][t][3*m+n] for t in range(len(arrays['U'])))
        bad+=val != int(i==m and j==k and l==n)
    return int(bad)

for name in ['laderman23','sun23','laderman_six_parameter_example']:
    data=read(f'round1/data/{name}.json')
    assert check_coefficients(data)==0
    report[name]={'exact_tensor_coefficients':729}

tor=read('round1/proofs/laderman_torus.json')
data=read('round1/data/laderman23.json')
z=[s.Rational((i%7)+2, (i%5)+1)*(-1 if i%3==0 else 1) for i in range(58)]
for (g,t,c),row in zip(tor['labels'],tor['final']['E']):
    key=('U','V','W')[g]
    data[key][t][c]=str(s.Rational(data[key][t][c])*s.prod(x**e for x,e in zip(z,row)))
assert check_coefficients(data)==0
data['U'][0][0]=str(s.Rational(data['U'][0][0])+1)
assert check_coefficients(data)>0
report['independent_58_parameter_instance']={'exact_coefficients':729,'mixed_sign_nonunit_rational_parameters':True,'corruption_rejected':True}

for name in ['exact_five_blocks','exact_all_rank_two_five']:
    d=read(f'round2/data/{name}.json')
    U,V,W,X,Y=([mat(v) for v in d[key]] for key in ['U','V','W','X','Y'])
    assert all(W[t]==X[t]*Y[t].T for t in range(5))
    for a,b in product(range(5),repeat=2):
        assert X[a].T*U[b]*V[a]*Y[b]==(s.eye(2) if a==b else s.zeros(2))
    ranks=[[m.rank() for m in rows] for rows in (U,V,W)]
    assert ranks == ([[2]*5,[3,2,2,2,2],[2]*5] if name=='exact_five_blocks' else [[2]*5]*3)
    assert check_coefficients(d)>0
    report[name]={'block_equations':100,'factorizations':5,'matrix_ranks':ranks,'not_full_multiplication_identity':True}

cert=read('round2/certificates/sun_four_block_extension.json')
sun=read('round1/data/sun23.json')
variables=s.symbols('u0:9');U=s.Matrix(3,3,variables)
parts=[]
for f in cert['factorizations']:
    X,Y=mat(f['X']),mat(f['Y']);t=f['slot']
    assert X*Y.T==mat(sun['W'][t]) and X.rank()==Y.rank()==2
    parts.append(X.T*U*mat(sun['V'][t]))
F=s.Matrix.vstack(*parts)
def minor(M,rr,cc):return M[rr[0],cc[0]]*M[rr[1],cc[1]]-M[rr[0],cc[1]]*M[rr[1],cc[0]]
for rec in cert['minor_identities']:
    rhs=sum(s.Rational(c['coefficient'])*minor(F,c['rows'],c['columns']) for c in rec['combination'])
    assert s.Poly(minor(U,rec['target_rows'],rec['target_columns'])-rhs,*variables).is_zero
assert len(cert['minor_identities'])==9
report['sun_extension']={'symbolic_quadratic_identities':9,'rational_symbolic_expansion_no_sampling':True}

# Reconstruct all original/core coordinates; prove the 17 extra ideal generators.
M={(3*i+j,3*j+k,3*k+i) for i,j,k in product(range(3),repeat=3)}
core=set(product([3,6],[3,4,6,7],[6,7]));assert len(M)==27 and len(core)==16 and M.isdisjoint(core)
coords={v:0 for v in M}|{v:i+1 for i,v in enumerate(sorted(core))}
def minorsymbol(a,b,axis):
    c=list(a);d=list(b);c[axis],d[axis]=d[axis],c[axis]
    r=Counter()
    if a in coords and b in coords:r[tuple(sorted([coords[a],coords[b]]))]+=1
    if tuple(c) in coords and tuple(d) in coords:r[tuple(sorted([coords[tuple(c)],coords[tuple(d)]]))]-=1
    return {k:v for k,v in r.items() if v}
assert minorsymbol((0,0,0),(4,3,1),0)=={(0,0):1}
for c in core:assert minorsymbol((0,0,0),c,0)=={(0,coords[c]):1}
# Independent full quadratic span, from every pair of nonzero coordinates in every flattening.
polys=[]
for a,b in combinations(coords,2):
    for axis in range(3):
        v=minorsymbol(a,b,axis)
        if v:polys.append(v)
monomials=list(combinations(range(17),2))+[(i,i) for i in range(17)]
space=s.polys.matrices.DomainMatrix.from_Matrix(s.Matrix([[q.get(m,0) for m in monomials] for q in polys]))
assert space.rank()==63
report['ac03_restricted_ideal']={'full_quadratic_span_rank':63,'extra_lambda_monomials':17,'core_support':16,'matrix_multiplication_support':27}

# Exact Fourier average after character orthogonality, retaining every coefficient.
def compression(p,q,n):
    N=p*q+1;J=list(range(p));R=[p*i for i in range(1,q+1)]
    K=(J+[i for i in range(N) if i not in J+R])[:n];H=K+R
    assert len(K)==n and set(K).isdisjoint(R)
    w={h:(2 if h in R else 0 if h in J else 1) for h in H}
    full=Counter()
    for ell,h,k in product(range(N),H,K):
        if (ell-h+k)%N==0:
            degree=(0 if ell==0 else 2)+w[k]-w[h]
            full[(ell,h,k,degree)]+=1
    assert not any(degree<0 and c for (*_,degree),c in full.items())
    constant={(ell,h,k):v for (ell,h,k,d),v in full.items() if d==0 and v}
    want={(0,k,k):1 for k in K}|{((r-j)%N,r,j):1 for r,j in product(R,J)}
    assert constant==want
    return N,K,R,full
g=[]
for axis,parameters in enumerate([(2,8,9),(4,4,9),(2,8,9)]):
    N,K,R,full=compression(*parameters)
    residual=Counter()
    for (*_,d),value in full.items():
        if d:residual[d]+=abs(value)
    other=[i for i in range(3) if i!=axis]
    small=sorted({c[axis] for c in core})
    singleton=small+[i for i in range(9) if i not in small]
    k_to_singleton=dict(zip(K,singleton))
    grouped_core=sorted({tuple(c[i] for i in other) for c in core})
    h_to_physical={h:[tuple(c[i] for i in other) for c in M if c[axis]==k_to_singleton[h]] for h in K}
    h_to_physical.update({h:[c] for h,c in zip(R,grouped_core)})
    physical=Counter()
    for (ell,h,k,d),value in full.items():
        for v in h_to_physical[h]:
            coord=[None]*3;coord[axis]=k_to_singleton[k]
            for i,ci in zip(other,v):coord[i]=ci
            physical[(ell,*coord,d)]+=value
    physical_constant={key[:-1]:value for key,value in physical.items() if key[-1]==0}
    expected={(0,*c):1 for c in M}
    for r,j in product(R,K[:parameters[0]]):
        coord=[None]*3;coord[axis]=k_to_singleton[j]
        for i,ci in zip(other,h_to_physical[r][0]):coord[i]=ci
        expected[((r-j)%N,*coord)]=1
    assert physical_constant==expected and len(expected)==43
    physical_residual=Counter()
    for key,value in physical.items():
        if key[-1]>0:physical_residual[key[-1]]+=abs(value)
    assert sum(physical_residual.values())==[272,236,272][axis]
    middle=s.zeros(9)
    for values in h_to_physical.values():
        for i,j in values:middle[i,j]+=1
    assert middle.rank()==4
    g.append({'parameters':parameters,'rank':N,'constant_terms':len([k for k in full if k[-1]==0]),'residual_coefficients_by_degree':dict(residual),'physical_constant_terms':43,'physical_residual_coefficients_by_degree':dict(physical_residual),'physical_residual_total':sum(physical_residual.values()),'merged_factor_rank_at_t1_index0':4})
report['ac03_grouped_fourier']=g

# Pair-plane reduced-section tangent intersection: eight core coordinate points
# and one noncoordinate rational point, supplemental to the universal rank proof.
E=[]
for i,k in product(range(3),repeat=2):
    A=s.zeros(9)
    for j in range(3):A[3*i+j,3*j+k]=1
    E.append(s.Matrix(81,1,list(A)))
for a,b in product([3,6],[3,4,6,7]):
    A=s.zeros(9);A[a,b]=1;E.append(s.Matrix(81,1,list(A)))
Em=s.Matrix.hstack(*E);assert Em.rank()==17
def tangent_dimension(a,b):
    cols=[]
    for i in range(9):
        e=s.eye(9)[:,i];cols += [s.Matrix(81,1,list(a*e.T)),s.Matrix(81,1,list(e*b.T))]
    T=s.Matrix.hstack(*cols)
    return 17+T.rank()-s.Matrix.hstack(Em,T).rank()
for a,b in product([3,6],[3,4,6,7]):assert tangent_dimension(s.eye(9)[:,a],s.eye(9)[:,b])==5
a=s.Matrix([0,0,0,2,0,0,-1,0,0]);b=s.Matrix([0,0,0,3,0,0,5,-2,0]);assert tangent_dimension(a,b)==5
report['ac03_pair_tangent_checks']={'rational_points':9,'affine_intersection_dimension':5,'projective_dimension':4}

(out/'independent-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

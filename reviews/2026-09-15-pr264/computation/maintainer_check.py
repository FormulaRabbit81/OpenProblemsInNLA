"""Independent MF-24 checks via Cauchy--Binet and path matchings.

No imports from the submission. Exact matching polynomials retain eta, rho=|z|^2,
and the Laurent variable t^2 simultaneously. Finite checks support, but do not
replace, the all-size written proof. Run with --out /path/to/results.json.
"""
from collections import defaultdict
from fractions import Fraction as F
from math import prod, isqrt
from pathlib import Path
import argparse
import json
import platform
import sympy as sp

def require(ok, why):
    if not ok:
        raise AssertionError(why)

def heights(m, side):
    k=m+1
    return [int(v%k!=0)+int(v//k>=1 if side=='X' else v//k==m)
            for v in range(k*k)]

def word(m, side):
    h=heights(m,side)
    return [b-a for a,b in zip(h,h[1:])]

def matching_polynomial(exponents):
    """det(eta I + (W-zI)* (W-zI)), as (eta,rho,t^2) exponents.

    The bipartite graph of W-zI is the path C0-R0-C1-R1-... .
    Each square minor has at most one perfect matching (a path has no cycles).
    Cauchy--Binet therefore gives the sum of weights of ALL partial matchings,
    with eta^(N-k) for a k-edge matching. Adjacent path edges cannot coexist.
    Diagonal edges have weight rho; shift edges have weight (t^2)^exponent.
    """
    n=len(exponents)+1
    edge_weights=[]
    for i in range(n):
        edge_weights.append((1,0))
        if i<n-1:edge_weights.append((0,exponents[i]))
    skip={(0,0,0):1};take={}
    for rho_power,t_power in edge_weights:
        new_skip=defaultdict(int,skip)
        for key,value in take.items():new_skip[key]+=value
        new_take={(k+1,r+rho_power,t+t_power):value
                  for (k,r,t),value in skip.items()}
        skip,take=dict(new_skip),new_take
    total=defaultdict(int,skip)
    for key,value in take.items():total[key]+=value
    return {(n-k,r,t):value for (k,r,t),value in total.items()}

def evaluate(poly,eta,rho,t_squared):
    return sum(F(c)*eta**e*rho**r*t_squared**t for (e,r,t),c in poly.items())

def rational_shift(m,t,side):
    w=sp.zeros((m+1)**2)
    for i,e in enumerate(word(m,side)):w[i,i+1]=sp.Rational(t**e)
    return w

def sylvester_positive(matrix):
    require(matrix==matrix.T,'non-symmetric candidate')
    minors=[matrix[:i,:i].det(method='domain-ge') for i in range(1,matrix.rows+1)]
    require(all(v>0 for v in minors),'non-positive leading principal minor')
    return minors

def check(out):
    record={'python':platform.python_version(),'sympy':sp.__version__}
    poly_results=[]
    polynomials={}
    for m in range(2,9):
        px=matching_polynomial(word(m,'X'));py=matching_polynomial(word(m,'Y'))
        require(px==py,f'full Laurent matching polynomial mismatch, m={m}')
        require(all(c>0 for c in px.values()),'non-positive matching coefficient')
        require(px[((m+1)**2,0,0)]==1,'wrong empty matching')
        polynomials[m]=px
        poly_results.append({'m':m,'N':(m+1)**2,'monomials':len(px),
                             'all_eta_rho_t_squared_Laurent_coefficients_equal':True})
    record['symbolic_matching_polynomials']=poly_results
    dense_count=0
    for m in (2,3):
        for t in (F(3,2),F(7,5)):
            for z,eta in ((sp.Rational(0),F(1,3)),(sp.Rational(2)+3*sp.I,F(2)),(-1+sp.I,F(3,5))):
                rho=sp.expand(sp.conjugate(z)*z)
                expected=evaluate(polynomials[m],eta,F(rho),t*t)
                for side in ('X','Y'):
                    W=rational_shift(m,t,side)
                    shifted=W-z*sp.eye(W.rows)
                    gram=shifted.conjugate().T*shifted+sp.Rational(eta)*sp.eye(W.rows)
                    got=gram.det(method='domain-ge')
                    require(sp.simplify(got-sp.Rational(expected))==0,'dense complex Gram differs from matching polynomial')
                    dense_count+=1
    record['direct_exact_complex_gram_determinants']=dense_count
    certificates=[]
    for m in (4,9):
        t=F(m);D=m+2;N=(m+1)**2
        wx=[t**e for e in word(m,'X')]
        wy=[t**e for e in word(m,'Y')]
        row=[prod(wx[:j*D]) for j in range(1,m+1)]
        require(sum(v*v for v in row)==m*t**4,'numerator row')
        require(prod(wy)==t*t,'denominator endpoint')
        bound=t*t+m-1
        all_minors=[]
        for residue in range(D):
            vertices=list(range(residue,N,D))
            B=sp.zeros(len(vertices))
            for i,v in enumerate(vertices):
                for j in range(i+1,len(vertices)):
                    B[i,j]=sp.Rational(prod(wy[v:vertices[j]]))
            all_minors+=sylvester_positive(sp.Rational(bound**2)*sp.eye(B.cols)-B.T*B)
        require(isqrt(m)**2==m,'non-square certificate parameter')
        certificates.append({'m':m,'t':int(t),'positive_principal_minors':len(all_minors),
                             'smallest_principal_minor':str(min(all_minors)),
                             'strict_ratio_lower_bound':str(t*t*isqrt(m)/bound)})
    record['independent_sylvester_norm_certificates']=certificates
    # Dense powers check all entries, including zeros, and the maximum degree.
    direct_count=0
    for m in (2,3,4):
        t=F(5,3);D=m+2;N=(m+1)**2
        for side in ('X','Y'):
            W=rational_shift(m,t,side);P=sp.zeros(N)
            for j in range(1,m+1):P+=W**(j*D)
            h=heights(m,side)
            for i in range(N):
                for j in range(N):
                    target=sp.Rational(t**(h[j]-h[i])) if j>i and (j-i)%D==0 else 0
                    require(P[i,j]==target,'full polynomial matrix mismatch')
            require(P[0,N-1]==t*t,'highest polynomial degree omitted')
            require((P-W**(m*D))[0,N-1]==0,'degree-truncation control undetected')
            direct_count+=1
    record['full_exact_polynomial_matrices']=direct_count
    # Equal unshifted singular values (same weight multiset) are insufficient.
    m=4;e=word(m,'Y');bad=e[:]
    a,b=(m-1)*(m+1)-1,m*(m+1)-1
    bad[a],bad[b]=bad[b],bad[a]
    require(sorted(e)==sorted(bad),'control changed unshifted singular values')
    pb=matching_polynomial(bad)
    require(pb!=polynomials[m],'misplaced bridge escaped symbolic test')
    good_at=evaluate(polynomials[m],F(1),F(1),F(4)**2)
    bad_at=evaluate(pb,F(1),F(1),F(4)**2)
    require(good_at!=bad_at,'misplaced bridge escaped concrete shifted test')
    try:sylvester_positive(sp.diag(1,0))
    except AssertionError:pass
    else:raise AssertionError('semidefinite matrix accepted as positive definite')
    # All coefficients collapse to the identical matrix when t=1.
    for m in range(2,9):
        require(evaluate(polynomials[m],F(2,3),F(7,5),F(1))
                ==evaluate(matching_polynomial([0]*((m+1)**2-1)),F(2,3),F(7,5),F(1)),
                't=1 control')
    record['controls']={'misplaced_bridge_same_weight_multiset':'rejected',
                        'concrete_shift_z1_eta1_bad_minus_good':str(bad_at-good_at),
                        'semidefinite_positive_definite_confusion':'rejected',
                        'highest_degree_omission':'detected',
                        'coincident_t1':'passed for m=2,...,8'}
    record['result']='PASS'
    record['limits']='Finite-dimensional exact checks, including symbolic t and complex-shift invariants; all-m quantifiers and unboundedness require the separately reviewed written proof.'
    out.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    check(parser.parse_args().out)

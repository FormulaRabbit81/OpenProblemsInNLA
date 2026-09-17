"""Independent exact review of the 63-parameter seven-product contact family.

Evaluates the FULL degree-112 polynomial and reconstructs its Jacobian by
explicit reverse chain rules, rather than the author's forward jets. Uses a
different, coarser Hessian bound G''(R) from a positive univariate majorant.
No author code, Decimal arithmetic, NumPy, or numerical search is imported.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,sys,time

class ZI:
    __slots__=('r','i')
    def __init__(self,r=0,i=0): self.r=int(r);self.i=int(i)
    def __add__(a,b):return ZI(a.r+b.r,a.i+b.i)
    def __neg__(a):return ZI(-a.r,-a.i)
    def __sub__(a,b):return a+-b
    def __mul__(a,b):return ZI(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r)
    def times(a,n):return ZI(a.r*n,a.i*n)
    def norm(a):return abs(a.r)+abs(a.i)
    def __bool__(a):return bool(a.r or a.i)
    def pair(a):return [str(a.r),str(a.i)]

DELTA=1
class Poly:
    # Coefficient Gaussian integers, common denominator DELTA**e.
    def __init__(self,cs=None,e=0):
        self.cs=list(cs if cs is not None else [ZI()]);self.e=e
        while len(self.cs)>1 and not self.cs[-1]:self.cs.pop()
    def __add__(a,b):
        e=max(a.e,b.e); sa=DELTA**(e-a.e);sb=DELTA**(e-b.e)
        c=[ZI() for _ in range(max(len(a.cs),len(b.cs)))]
        for i,v in enumerate(a.cs):c[i]=c[i]+v.times(sa)
        for i,v in enumerate(b.cs):c[i]=c[i]+v.times(sb)
        return Poly(c,e)
    def __mul__(a,b):
        c=[ZI() for _ in range(len(a.cs)+len(b.cs)-1)]
        for i,v in enumerate(a.cs):
            if v:
                for j,w in enumerate(b.cs):
                    if w:c[i+j]=c[i+j]+v*w
        return Poly(c,a.e+b.e)
    def times(a,n):return Poly([v.times(n) for v in a.cs],a.e)
    def shift(a,j):return Poly([ZI() for _ in range(j)]+a.cs,a.e)
    def numerators(a,e):
        assert e>=a.e
        return [v.times(DELTA**(e-a.e)) for v in a.cs]

def full_value_and_reverse_jacobian(theta,active):
    monomials=[Poly([ZI(1)]).shift(j) for j in range(5)]
    scalars=[Poly([v],1) for v in theta]
    def linear(start,basis):
        result=Poly()
        for j,p in enumerate(basis):result=result+scalars[start+j]*p
        return result
    A=Poly(theta[:15],1);B=Poly(theta[15:24],1)
    S=A*A+B;E=monomials+[A,S]
    L=linear(24,E);R=linear(31,E);T=L*R
    F=E+[T]
    U=linear(38,F);V=linear(46,F);H=U*V
    basis=F+[H];out=linear(54,basis)
    assert out.e==15 and len(out.cs)<=113

    # Reverse derivatives w.r.t. the polynomial intermediate quantities.
    wH=scalars[62]
    wT=scalars[61]+wH*(scalars[45]*V+scalars[53]*U)
    wS=scalars[60]+wT*(scalars[30]*R+scalars[37]*L)+wH*(scalars[44]*V+scalars[52]*U)
    wA=scalars[59]+wT*(scalars[29]*R+scalars[36]*L)+wH*(scalars[43]*V+scalars[51]*U)+(A*wS).times(2)
    derivatives=[wA.shift(j) for j in range(15)]+[wS.shift(j) for j in range(9)]
    leftT=wT*R;rightT=wT*L;leftH=wH*V;rightH=wH*U
    derivatives += [leftT*p for p in E]+[rightT*p for p in E]
    derivatives += [leftH*p for p in F]+[rightH*p for p in F]+basis
    assert len(derivatives)==63
    assert all(len(p.cs)<=113 and p.e<=15 for p in derivatives)
    vals=out.numerators(15)
    cols=[derivatives[j].numerators(15) for j in active]
    return vals,cols

def int_add(a,b):
    r=[0]*max(len(a),len(b))
    for i,v in enumerate(a):r[i]+=v
    for i,v in enumerate(b):r[i]+=v
    return r
def int_mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):r[i+j]+=v*w
    return r
def majorant_coefficients():
    # Set every scalar parameter equal to R and x=1. All coefficients in the
    # structural map are nonnegative integers, so this is a total majorant.
    E=[5,24,225]
    T=[0,0]+int_mul(E,E)
    W=int_add(E,T)
    H=[0,0]+int_mul(W,W)
    return [0]+int_add(W,H)

def main(path):
    global DELTA
    start=time.monotonic();raw=path.read_bytes();cert=json.loads(raw)
    D=int(cert['degree']);N=D+1;active=cert['active_parameters']
    assert len(active)==N and len(set(active))==N and all(0<=j<63 for j in active)
    DELTA=int(cert['theta_denominator']);IDELTA=int(cert['inverse_denominator'])
    assert DELTA>0 and IDELTA>0
    theta=[ZI(r,i) for r,i in cert['theta_numerators']]
    inverse=[[ZI(r,i) for r,i in row] for row in cert['inverse_numerators']]
    assert len(theta)==63 and len(inverse)==N and all(len(row)==N for row in inverse)
    vals,columns=full_value_and_reverse_jacobian(theta,active)
    assert len(vals)==113
    denominator=DELTA**15
    residual=vals[:N];residual[D]=residual[D]-ZI(denominator)
    jac=[[col[i] if i<len(col) else ZI() for col in columns] for i in range(N)]
    residual_bounds=[];defect_rows=[]
    for row in range(N):
        value=ZI()
        for k in range(N):value=value+inverse[row][k]*residual[k]
        residual_bounds.append(value.norm())
        defect_sum=0
        for column in range(N):
            value=ZI()
            for k in range(N):value=value+inverse[row][k]*jac[k][column]
            if row==column:value=value-ZI(denominator*IDELTA)
            defect_sum+=value.norm()
        defect_rows.append(defect_sum)
    eta=Q(max(residual_bounds),denominator*IDELTA)
    defect=Q(max(defect_rows),denominator*IDELTA)
    inverse_norm=Q(max(sum(v.norm() for v in row) for row in inverse),IDELTA)
    assert eta==Q(cert['preconditioned_residual_bound'])
    assert defect==Q(cert['inverse_defect_bound'])
    assert inverse_norm==Q(cert['inverse_norm_bound'])

    radius=Q(cert['radius']);assert radius>0
    parameter_bound=Q(max(v.norm() for v in theta),DELTA)+radius
    R=(parameter_bound.numerator+parameter_bound.denominator-1)//parameter_bound.denominator
    assert R>=parameter_bound
    G=majorant_coefficients()
    hessian=sum(i*(i-1)*v*R**(i-2) for i,v in enumerate(G) if i>=2)
    q=defect+inverse_norm*hessian*radius
    self_bound=eta+q*radius
    assert defect<1 and q<Q(1,2) and self_bound<radius
    # Bind all full coefficients and reverse derivatives without emitting them.
    full_payload={'denominator':str(denominator),'coefficients':[v.pair() for v in vals],
                  'active':active,'jacobian_columns':[[v.pair() for v in col] for col in columns]}
    full_digest=hashlib.sha256(json.dumps(full_payload,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    result={'status':'PASS','degree':D,'source_certificate':str(path),
      'source_certificate_sha256':hashlib.sha256(raw).hexdigest(),
      'method':'full degree-112 values and explicit reverse chain Jacobian; independent scalar majorant G second derivative',
      'full_output_degree':112,'low_rows':N,'active_parameters':active,
      'author_eta_defect_inverse_norm_match_exactly':True,
      'preconditioned_residual_bound':str(eta),'inverse_defect_bound':str(defect),
      'inverse_norm_bound':str(inverse_norm),'radius':str(radius),
      'uniform_parameter_norm_bound_R':R,'G_coefficients':G,
      'independent_hessian_bound':str(hessian),'independent_contraction_bound':str(q),
      'independent_self_map_bound':str(self_bound),
      'contraction_less_than_half':True,'self_map_strictly_inside_ball':True,
      'full_value_and_jacobian_sha256':full_digest,
      'proof_consequence':f'V{D} subset X7, using the separately reviewed membership and weighted scaling arguments',
      'elapsed_seconds':time.monotonic()-start}
    dest=Path(__file__).with_name(f'seven-contact-degree{D}-fresh-check.json')
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS degree',D,'full degree112; exact bounds match.')
    print('Independent Hessian bound',hessian,'R',R,'q <',float(q),'; runtime',result['elapsed_seconds'])
    print('Saved',dest)

if __name__=='__main__':
    default=Path(__file__).resolve().parents[1]/'experiments/upper_contact46_certify.json'
    main(Path(sys.argv[1]) if len(sys.argv)>1 else default)

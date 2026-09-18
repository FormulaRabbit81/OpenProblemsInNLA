"""Fresh exact D47 certificate reconstruction in the actual seven-product chart.

Imports only the earlier independent reviewer's elementary Gaussian-integer
polynomial arithmetic. No author code is imported. Evaluates all 129 output
coefficients and computes derivatives by a reverse pass through the four
normalized product gates. A different global majorant G''(R) bounds Hessians.
"""
from fractions import Fraction as Q
from pathlib import Path
import importlib.util,hashlib,json,time

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('fresh_review_arithmetic',HERE/'seven-contact-fresh-check.py')
ar=importlib.util.module_from_spec(spec);spec.loader.exec_module(ar)
ZI,Poly=ar.ZI,ar.Poly

def evaluate_reverse(theta):
    parameters=[Poly([z],1) for z in theta]
    one=Poly([ZI(1)])
    x=[one.shift(j) for j in range(5)]
    alpha,b,c,eta=parameters[:4]
    quartic=x[4]+alpha*x[3]
    third=quartic*quartic+b*x[2]*quartic+c*x[1]*quartic+eta*x[3]
    basis=x[:3]+[quartic,third]
    cursor=4;gates=[]
    for _ in range(4):
        low=list(range(1,len(basis)-1));left=basis[-1];right=basis[-1]
        li=list(range(cursor,cursor+len(low)));cursor+=len(low)
        ri=list(range(cursor,cursor+len(low)));cursor+=len(low)
        for j,param in zip(low,li):left=left+parameters[param]*basis[j]
        for j,param in zip(low,ri):right=right+parameters[param]*basis[j]
        gates.append((len(basis),low,li,ri,left,right))
        basis.append(left*right)
    assert cursor==40 and len(basis)==9
    out=Poly()
    for j,p in enumerate(basis):out=out+parameters[40+j]*p
    assert out.e==33 and len(out.cs)==129

    derivatives=[None]*49
    adj=[p for p in parameters[40:49]]
    for gate,low,li,ri,left,right in reversed(gates):
        w=adj[gate]
        left_sens=w*right;right_sens=w*left
        adj[gate-1]=adj[gate-1]+left_sens+right_sens
        for j,lp,rp in zip(low,li,ri):
            derivatives[lp]=left_sens*basis[j]
            derivatives[rp]=right_sens*basis[j]
            adj[j]=adj[j]+left_sens*parameters[lp]+right_sens*parameters[rp]
    derivatives[0]=(adj[3]+adj[4]*(quartic.times(2)+b*x[2]+c*x[1]))*x[3]
    derivatives[1]=adj[4]*x[2]*quartic
    derivatives[2]=adj[4]*x[1]*quartic
    derivatives[3]=adj[4]*x[3]
    derivatives[40:49]=basis
    assert all(p is not None and p.e<=33 and len(p.cs)<=129 for p in derivatives)
    return out.numerators(33),[p.numerators(33) for p in derivatives]

def majorant():
    add,mul=ar.int_add,ar.int_mul
    parameter=[0,1];q=[1,1];r=[1,5,3]
    basis=[[1],[1],[1],q,r]
    for _ in range(4):
        lower=[0]
        for p in basis[1:-1]:lower=add(lower,p)
        factor=add(basis[-1],mul(parameter,lower))
        basis.append(mul(factor,factor))
    total=[0]
    for p in basis:total=add(total,p)
    return mul(parameter,total)

def main():
    start=time.monotonic();root=HERE.parent
    seed_path=root/'experiments/lower_full49_seed.json'
    cert_path=root/'experiments/lower_full49_certify.json'
    seed_raw=seed_path.read_bytes();cert_raw=cert_path.read_bytes()
    seed=json.loads(seed_raw);cert=json.loads(cert_raw)
    active=seed['active_parameters'];assert len(active)==48 and len(set(active))==48
    assert all(0<=j<49 for j in active)
    assert active==cert['active_parameters'] and cert['degree']==47
    delta=int(seed['theta_denominator']);inv_delta=int(seed['inverse_denominator'])
    assert delta==10**70 and inv_delta==10**60
    ar.DELTA=delta
    theta=[ZI(r,i) for r,i in seed['theta_numerators']]
    inverse=[[ZI(r,i) for r,i in row] for row in seed['inverse_numerators']]
    assert len(theta)==49 and len(inverse)==48 and all(len(row)==48 for row in inverse)
    values,all_cols=evaluate_reverse(theta)
    print('Fresh full degree128 map and reverse derivatives evaluated',time.monotonic()-start,flush=True)
    denominator=delta**33
    residual=values[:48];residual[47]=residual[47]-ZI(denominator)
    cols=[all_cols[j] for j in active]
    jac=[[col[i] if i<len(col) else ZI() for col in cols] for i in range(48)]
    residual_rows=[];defect_rows=[]
    for i in range(48):
        v=ZI()
        for k in range(48):v=v+inverse[i][k]*residual[k]
        residual_rows.append(v.norm());row=0
        for j in range(48):
            v=ZI()
            for k in range(48):v=v+inverse[i][k]*jac[k][j]
            if i==j:v=v-ZI(denominator*inv_delta)
            row+=v.norm()
        defect_rows.append(row)
    eta=Q(max(residual_rows),denominator*inv_delta)
    defect=Q(max(defect_rows),denominator*inv_delta)
    inverse_norm=Q(max(sum(v.norm() for v in row) for row in inverse),inv_delta)
    assert eta==Q(cert['preconditioned_residual_bound'])
    assert defect==Q(cert['inverse_defect_bound'])
    assert inverse_norm==Q(cert['inverse_norm_bound'])
    radius=Q(cert['radius']);assert radius==Q(1,10**45)
    chart_distance=abs(Q(theta[1].r,delta)-2)
    assert chart_distance>radius and chart_distance==Q(cert['b_real_distance_from_2'])
    scalar_bound=Q(max(v.norm() for v in theta),delta)+radius
    R=(scalar_bound.numerator+scalar_bound.denominator-1)//scalar_bound.denominator
    coeffs=majorant();assert len(coeffs)==34 and all(v>=0 for v in coeffs)
    Hessian=sum(n*(n-1)*v*R**(n-2) for n,v in enumerate(coeffs) if n>=2)
    contraction=defect+inverse_norm*Hessian*radius
    self_map=eta+contraction*radius
    assert defect<1 and contraction<Q(1,2) and self_map<radius
    assert eta<Q(1,10**69) and defect<Q(1,10**57) and inverse_norm<4000
    # Streaming canonical digest of full exact arrays, without huge output.
    digest=hashlib.sha256()
    for label,polys in [('value',[values]),('derivatives',all_cols)]:
        digest.update(label.encode())
        for poly in polys:
            digest.update(b'[')
            for v in poly:digest.update((str(v.r)+','+str(v.i)+';').encode())
            digest.update(b']')
    result={'status':'PASS','degree':47,'parameter_count':49,
      'method':'Full degree128 polynomial values and reverse derivatives; independent uniform-parameter majorant',
      'seed_sha256':hashlib.sha256(seed_raw).hexdigest(),
      'author_certificate_sha256':hashlib.sha256(cert_raw).hexdigest(),
      'active_parameters':active,'full_polynomial_degree':128,
      'parameter_degree_bound':33,'value_denominator':str(denominator),
      'preconditioned_residual_bound':str(eta),'inverse_defect_bound':str(defect),
      'inverse_norm_bound':str(inverse_norm),'radius':str(radius),
      'exact_author_eta_defect_inverse_norm_match':True,
      'b_real_distance_from_2':str(chart_distance),
      'uniform_parameter_norm_bound_R':R,'G_coefficients':coeffs,
      'independent_hessian_bound':str(Hessian),
      'independent_contraction_bound':str(contraction),
      'independent_self_map_bound':str(self_map),
      'contraction_less_than_half':True,'self_map_strictly_inside_ball':True,
      'full_arrays_stream_sha256':digest.hexdigest(),
      'mathematical_consequence':'V47 subset X7 via the separately reviewed actual-chart and weighted-limit proofs',
      'elapsed_seconds':time.monotonic()-start}
    destination=HERE/'full49-degree47-fresh-check.json'
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: D47 full reverse reconstruction. H=',Hessian,'R=',R,'q=',float(contraction),flush=True)
    print('Saved',destination,'elapsed',result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()

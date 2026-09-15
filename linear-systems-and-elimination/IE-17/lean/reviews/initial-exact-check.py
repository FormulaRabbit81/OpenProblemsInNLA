"""Fresh exact IE-17 reconstruction. No repository code is imported.

The mathematical inputs are the manuscript's integer A,b,w and two cutoffs.
Krylov minimizers and all certificate matrices are recomputed. This is an
arithmetic precheck, not a proof of the operator-norm or infimum bridges.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import lcm
import json


def transpose(a):
    return [list(row) for row in zip(*a)]


def dot(x, y):
    return sum((a*b for a, b in zip(x, y)), Q(0))


def mul(a, b):
    return [[dot(row, col) for col in transpose(b)] for row in a]


def mv(a, x):
    return [dot(row, x) for row in a]


def inverse_and_det(a):
    n = len(a)
    aug = [[Q(z) for z in row] + [Q(i == j) for j in range(n)]
           for i, row in enumerate(a)]
    det = Q(1)
    for k in range(n):
        j = next(j for j in range(k, n) if aug[j][k])
        if j != k:
            aug[k], aug[j] = aug[j], aug[k]
            det = -det
        pivot = aug[k][k]
        det *= pivot
        aug[k] = [x/pivot for x in aug[k]]
        for i in range(n):
            if i != k:
                c = aug[i][k]
                aug[i] = [x-c*y for x, y in zip(aug[i], aug[k])]
    return [row[n:] for row in aug], det


def leading_minors(a):
    return [inverse_and_det([row[:k] for row in a[:k]])[1]
            for k in range(1, len(a)+1)]


def ldl(a):
    n = len(a)
    lower = [[Q(i == j) for j in range(n)] for i in range(n)]
    diagonal = []
    for j in range(n):
        diagonal.append(a[j][j]-sum(lower[j][k]**2*diagonal[k] for k in range(j)))
        assert diagonal[j] > 0
        for i in range(j+1, n):
            lower[i][j] = (a[i][j]-sum(lower[i][k]*lower[j][k]*diagonal[k]
                                      for k in range(j)))/diagonal[j]
    assert mul([[lower[i][j]*diagonal[j] for j in range(n)] for i in range(n)],
               transpose(lower)) == a
    return lower, diagonal


def encoded(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, list):
        return [encoded(x) for x in value]
    if isinstance(value, dict):
        return {k: encoded(v) for k, v in value.items()}
    return value


A = [[Q(z) for z in row] for row in [[1,0,0],[0,6,0],[0,0,5],[0,0,0]]]
b = list(map(Q, [11,1,1,1]))
H = mul(transpose(A), A)
C = mul(A, transpose(A))
g = mv(transpose(A), b)
columns = [g]
for k in range(2):
    columns.append(mv(H, columns[-1]))
data = []
for k in (1,2,3):
    V = transpose(columns[:k])
    HV = mul(H,V)
    gram = mul(transpose(HV),HV)
    gram_inv, gram_det = inverse_and_det(gram)
    assert gram_det > 0
    coeff = mv(gram_inv,mv(transpose(HV),g))
    x = mv(V,coeff)
    z = mv(A,x)
    residual = [a-c for a,c in zip(b,z)]
    normal = mv(transpose(A),residual)
    assert mv(transpose(HV), normal) == [0]*k
    s, rr = dot(x,x),dot(residual,residual)
    D = [[(rr*(i==j)-residual[i]*residual[j]+z[i]*z[j])/s
          for j in range(4)] for i in range(4)]
    gram_scaled = [[s*H[i][j]+rr*(i==j) for j in range(3)] for i in range(3)]
    approx = dot(normal,mv(inverse_and_det(gram_scaled)[0],normal))
    data.append(dict(k=k, V=V, coefficients=coeff, normal_equation_gram=gram,
                     gram_determinant=gram_det, x=x, z=z, residual=residual,
                     normal_residual=normal, squared_x_norm=s,
                     squared_residual_norm=rr, squared_normal_residual_norm=dot(normal,normal),
                     D=D, approximation_scaled_gram=gram_scaled,
                     approximation_squared=approx))

assert data[0]['x'] == [Q(z,31201) for z in [11231,6126,5105]]
assert data[1]['x'] == [Q(z,55219) for z in [87659,7599,16865]]
assert data[2]['x'] == [Q(11),Q(1,6),Q(1,5)]
assert data[0]['normal_residual'] != [0]*3
assert data[1]['normal_residual'] != [0]*3
assert data[2]['normal_residual'] == [0]*3
assert inverse_and_det(transpose(columns))[1] == -3049200

w = list(map(Q,[250,-1,1,27]))
omega = dot(w,w)
kappa = Q(1979,2000)
first = data[0]
s,z,residual,D = [first[k] for k in ['squared_x_norm','z','residual','D']]
h = dot(w,z)
c0 = [residual[i]-w[i]*dot(w,residual)/omega for i in range(4)]
a0 = [-mv(transpose(A),w)[j]+h*first['x'][j]/s for j in range(3)]
den = omega*s*kappa-h*h
assert den > 0
E = [[-w[i]*mv(transpose(A),w)[j]/omega+c0[i]*first['x'][j]/s
      +h*c0[i]*a0[j]/den for j in range(3)] for i in range(4)]
perturbed = [[A[i][j]+E[i][j] for j in range(3)] for i in range(4)]
new_residual = [x-y for x,y in zip(mv(perturbed,first['x']),b)]
assert mv(transpose(perturbed),new_residual) == [0]*3
EE = mul(transpose(E),E)
upper = [[kappa*(i==j)-EE[i][j] for j in range(3)] for i in range(3)]
upper_L,upper_D = ldl(upper)
upper_minors = leading_minors(upper)
assert all(x > 0 for x in upper_minors)
upper_T = [[Q(z) for z in row] for row in [[1,-18,23],[0,1,0],[0,0,1]]]
assert inverse_and_det(upper_T)[1] == 1
upper_congruence = mul(mul(transpose(upper_T),upper),upper_T)
upper_congruence_den = lcm(*(x.denominator for row in upper_congruence for x in row))
upper_congruence_num = [[x*upper_congruence_den for x in row]
                        for row in upper_congruence]
assert all(x.denominator == 1 for row in upper_congruence_num for x in row)
upper_congruence_margins = [upper_congruence_num[i][i]-
    sum(abs(upper_congruence_num[i][j]) for j in range(3) if i != j) for i in range(3)]
assert all(x > 0 for x in upper_congruence_margins)
E_den = lcm(*(x.denominator for row in E for x in row))
E_num = [[x*E_den for x in row] for row in E]
assert all(x.denominator == 1 for row in E_num for x in row)

second = data[1]
lower_den = Q(2407881992100)
lower = [[Q(5,6)*C[i][j]+second['D'][i][j]/6-Q(99,100)*(i==j)
          for j in range(4)] for i in range(4)]
K = [[lower_den*x for x in row] for row in lower]
assert all(x.denominator == 1 for row in K for x in row)
lower_minors = leading_minors(K)
assert lower_minors == list(map(Q,[206417059721,17265994657467102998545591,
    960941324740480331793743845178086291011,
    65442104145157248520714038046591467785805073713081]))
weights = list(map(Q,[10000,10,185,1287]))
strong_cutoff = Q(9901,10000)
strong_K = [[K[i][j]-lower_den*(strong_cutoff-Q(99,100))*(i==j)
             for j in range(4)] for i in range(4)]
margins = [strong_K[i][i]*weights[i]-sum(abs(strong_K[i][j])*weights[j]
           for j in range(4) if i != j) for i in range(4)]
assert all(x > 0 for x in margins)
zero_new_residual_ratio = second['squared_residual_norm']/second['squared_x_norm']
assert zero_new_residual_ratio > strong_cutoff
assert first['approximation_squared'] == Q(69694107852573439503892031925,
                                         69323394392991282508138323472)
assert second['approximation_squared'] == Q(5430772101137459612205263871781350,
                                          5387955615790281743396033884265233)
assert first['approximation_squared'] < Q(503,500) < Q(1007,1000) < second['approximation_squared']

result = dict(scope='Exact arithmetic pre-proof reconstruction, not Lean verification.',
    status='PASS', A=A,b=b,H=H,g=g,C=C,iterates=data,krylov3_determinant=Q(-3049200),
    upper=dict(w=w,omega=omega,kappa=kappa,h=h,completion_denominator=den,
        direction_C=dot(w,mv(C,w))/omega,direction_D=dot(w,mv(D,w))/omega,
        E=E,E_common_denominator=E_den,E_integer_numerator=E_num,
        gram=upper,gram_LDL_lower=upper_L,gram_LDL_diagonal=upper_D,
        simple_congruence=upper_T,
        congruence_common_denominator=upper_congruence_den,
        congruence_integer_numerator=upper_congruence_num,
        congruence_diagonal_dominance_margins=upper_congruence_margins,
        leading_principal_minors=upper_minors),
    lower=dict(t=Q(5,6),source_cutoff=Q(99,100),integer_matrix=K,
        denominator=lower_den,leading_principal_minors=lower_minors,
        stronger_cutoff=strong_cutoff,weights=weights,
        stronger_weighted_dominance_margins=margins,
        zero_new_residual_squared_ratio=zero_new_residual_ratio))
Path(__file__).with_suffix('.json').write_text(json.dumps(encoded(result),indent=2)+'\n')
print('PASS: exact Krylov minimizers, source upper/lower certificates, both approximation fractions, '
      'and stronger rational weighted-dominance lower bound.')

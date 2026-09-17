"""Independent exact audit of the MF-14 degree-44 continuation certificate.

The defining equations and zero-one point are transcribed from the supplied
chat. No prior verifier or stored Jacobian is imported. Sparse first-order
jets propagate all 45 derivatives at once without truncating powers of x.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import hashlib
import json


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def add(*polys):
    out = defaultdict(int)
    for poly in polys:
        for key, value in poly.items():
            out[key] += value
    return {key: value for key, value in out.items() if value}


def mul(left, right):
    out = defaultdict(int)
    for (degree, direction), coefficient in left.items():
        for (other_degree, other_direction), other in right.items():
            if direction >= 0 and other_direction >= 0:
                continue
            out[degree+other_degree, max(direction, other_direction)] += coefficient*other
    return {key: value for key, value in out.items() if value}


def monomial(degree):
    return {(degree, -1): 1}


def value(poly):
    return {key: coefficient for key, coefficient in poly.items() if key[1] == -1}


def determinant(matrix):
    a = [[Fraction(v) for v in row] for row in matrix]
    result = Fraction(1)
    pivots, swaps = [], []
    for k in range(len(a)):
        row = next((r for r in range(k, len(a)) if a[r][k]), None)
        require(row is not None, 'Singular integer matrix')
        if row != k:
            a[k], a[row] = a[row], a[k]
            result = -result
            swaps.append([k, row])
        pivot = a[k][k]
        result *= pivot
        pivots.append(str(pivot))
        for i in range(k+1, len(a)):
            multiplier = a[i][k]/pivot
            if not multiplier:
                continue
            a[i][k] = Fraction(0)
            for j in range(k+1, len(a)):
                a[i][j] -= multiplier*a[k][j]
    return result, pivots, swaps


def determinant_modulo(matrix, prime):
    a = [[v % prime for v in row] for row in matrix]
    result = 1
    for column in range(len(a)):
        row = next((r for r in range(column, len(a)) if a[r][column]), None)
        require(row is not None, 'Singular modular matrix')
        if row != column:
            a[column], a[row] = a[row], a[column]
            result = -result
        pivot = a[column][column]
        result = result*pivot % prime
        inv = pow(pivot, -1, prime)
        for i in range(column+1, len(a)):
            multiplier = a[i][column]*inv % prime
            for j in range(column, len(a)):
                a[i][j] = (a[i][j]-multiplier*a[column][j]) % prime
    return result


def main():
    powers = [3, 6, 7, 8, 9, 10, 11]
    names = ['alpha', 'beta'] + ['xi'+str(j) for j in powers]
    for prefix, count in [('u',4), ('v',3), ('a',5), ('b',3), ('c',6), ('d',6)]:
        names.extend(prefix+str(i) for i in range(1, count+1))
    names.extend('z'+str(i) for i in range(9))
    nonzero = {'alpha', 'b2', 'd3', 'd5', 'd6', 'z8'}
    point = [int(name in nonzero) for name in names]
    parameters = {name: {(0,-1): point[i], (0,i): 1}
                  for i, name in enumerate(names)}
    require(len(names) == len(set(names)) == 45, 'Parameter count')

    def combination(prefix, basis, first=1):
        return add(*(mul(parameters[prefix+str(i)], poly)
                     for i, poly in enumerate(basis, start=first)))

    one, x, x2 = (monomial(i) for i in range(3))
    Q = add(monomial(4), mul(parameters['alpha'], monomial(3)))
    R = add(monomial(5), mul(parameters['beta'], monomial(3)))
    P = add(monomial(12), *(mul(parameters['xi'+str(i)], monomial(i)) for i in powers))
    L3 = [x, x2, Q]
    L4 = L3+[R]
    L5 = L4+[P]
    F = mul(add(P, combination('u', L4)), add(R, combination('v', L3)))
    G = mul(add(F, combination('a', L5)), add(R, combination('b', L3)))
    L6 = L5+[F]
    H = mul(add(G, combination('c', L6)), add(G, combination('d', L6)))
    output = combination('z', [one, x, x2, Q, R, P, F, G, H], first=0)
    require(max(degree for degree, _ in F) == 17, 'F jet degree')
    require(max(degree for degree, _ in G) == 22, 'G jet degree')
    require(max(degree for degree, _ in H) == 44, 'H jet degree')
    require(max(degree for degree, _ in output) == 44, 'Output jet degree')
    matrix = [[output.get((row, col), 0) for col in range(45)] for row in range(45)]

    # Re-derive the columns by the chain rule at the zero-one point, grouping
    # the variation through F and G. These expressions do not use jet columns.
    q, r, p, f, g, h = map(value, [Q, R, P, F, G, H])
    require(q == add(monomial(4), monomial(3)), 'Base Q')
    require(r == monomial(5) and p == monomial(12) and f == monomial(17), 'Base R/P/F')
    require(g == add(monomial(22), monomial(19)), 'Base G')
    require(h == mul(g, add(g,q,p,f)), 'Base H')
    B = add(r, x2)
    K = add(g, g, q, p, f)
    L = add(mul(K,B), g)
    l3, l4, l5, l6 = [x,x2,q], [x,x2,q,r], [x,x2,q,r,p], [x,x2,q,r,p,f]
    formulas = [mul(g, monomial(3)), mul(add(mul(L,p),mul(K,f)), monomial(3))]
    formulas += [mul(add(mul(L,r),g),monomial(j)) for j in powers]
    formulas += [mul(mul(L,r),qj) for qj in l4]
    formulas += [mul(mul(L,p),qj) for qj in l3]
    formulas += [mul(mul(K,B),qj) for qj in l5]
    formulas += [mul(mul(K,f),qj) for qj in l3]
    formulas += [mul(add(g,q,p,f),qj) for qj in l6]
    formulas += [mul(g,qj) for qj in l6]
    formulas += [one,x,x2,q,r,p,f,g,h]
    require(len(formulas) == 45, 'Derivative formula count')
    require(all(matrix[i][j] == formulas[j].get((i,-1),0)
                for i in range(45) for j in range(45)), 'Analytic columns disagree')
    det, pivots, swaps = determinant(matrix)
    residues = {str(prime): determinant_modulo(matrix, prime) for prime in [3,101,1009]}
    require(det == 256, 'Claimed determinant')
    require(residues == {'3':1, '101':54, '1009':256}, 'Modular determinants')
    require(min(map(min, matrix)) == 0 and max(map(max, matrix)) == 6, 'Entry range')
    result = {
        'review_date': '2026-09-17',
        'scope': 'Continuation and exact Jacobian; joint border lemma reviewed separately',
        'method': 'Simultaneous sparse jets, explicit chain-rule columns, rational Gaussian elimination, modular elimination',
        'parameter_order': names,
        'parameter_point': point,
        'integer_jacobian': matrix,
        'exact_determinant': int(det),
        'modular_determinants': residues,
        'rational_elimination_pivots': pivots,
        'rational_elimination_swaps': swaps,
        'entry_range': [min(map(min,matrix)), max(map(max,matrix))],
        'analytical_columns_match_all_2025_entries': True,
        'intermediate_jet_degrees': {'Q':4,'R':5,'P':12,'F':17,'G':22,'H':44,'output':44},
        'all_x_powers_retained': True,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'passed': True,
    }
    target = Path(__file__).with_name('independent-degree44-certificate.json')
    target.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS: 45-parameter continuation, untruncated simultaneous jets, all analytic columns agree.')
    print('Exact rational determinant:', det)
    print('Independent modular determinants:', residues)
    print('Jacobian entry range: 0..6. Full certificate:', target.name)


if __name__ == '__main__':
    main()

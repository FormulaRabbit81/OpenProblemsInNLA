#!/usr/bin/env python3
"""Fresh MF-14 coefficient-map validation by exact interpolation.

Uses only Python's standard library. Does not read any prior verifier,
Jacobian table, stored matrix, or differentiation implementation.
The 45-parameter map is transcribed from the defining circuit equations.
Each directional derivative is recovered from 14 whole-circuit evaluations.
Polynomials are stored with their full coefficient lists, without truncation.
"""
from fractions import Fraction
from math import comb, lcm
from pathlib import Path
import json


def check(ok, message):
    if not ok:
        raise ArithmeticError(message)


def add(*args):
    out = [0] * max(map(len, args))
    for p in args:
        for i, v in enumerate(p):
            out[i] += v
    return trim(out)


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    out[i + j] += a * b
    return trim(out)


def monomial(d):
    return [0] * d + [1]


def lin(c, polys):
    check(len(c) == len(polys), 'Linear combination dimension mismatch')
    return add(*[[a * v for v in p] for a, p in zip(c, polys)])


JDEG = [3, 6, 7, 8, 9, 10, 11]
NAMES = ['alpha', 'beta'] + ['xi' + str(j) for j in JDEG]
for name, count in [('u',4), ('v',3), ('a',5), ('b',3), ('c',6), ('d',6)]:
    NAMES.extend(name + str(i) for i in range(1, count + 1))
NAMES.extend('z' + str(i) for i in range(9))
check(len(NAMES) == 45, 'Parameter count')
BASE = [int(n in ['alpha', 'b2', 'd3', 'd5', 'd6', 'z8']) for n in NAMES]


def evaluate(theta):
    check(len(theta) == 45, 'Parameter vector length')
    one, x, x2 = monomial(0), monomial(1), monomial(2)
    Q = add(monomial(4), lin([theta[0]], [monomial(3)]))
    R = add(monomial(5), lin([theta[1]], [monomial(3)]))
    P = add(monomial(12), lin(theta[2:9], [monomial(j) for j in JDEG]))
    L3 = [x, x2, Q]
    L4 = L3 + [R]
    L5 = L4 + [P]
    F = mul(add(P, lin(theta[9:13], L4)), add(R, lin(theta[13:16], L3)))
    G = mul(add(F, lin(theta[16:21], L5)), add(R, lin(theta[21:24], L3)))
    L6 = L5 + [F]
    H = mul(add(G, lin(theta[24:30], L6)), add(G, lin(theta[30:36], L6)))
    output = lin(theta[36:45], [one, x, x2, Q, R, P, F, G, H])
    check(len(F) <= 18 and len(G) <= 23 and len(H) <= 45,
          'Unexpected polynomial degree')
    return output


def interpolate_jacobian():
    # Coefficient degrees: Q,R,P <= 1; F <= 4; G <= 6; H <= 12;
    # z.output <= 13. Thus 14 samples recover a directional polynomial.
    n = 13
    scale = lcm(*range(1, n + 1))
    weights = [-sum(scale // k for k in range(1, n + 1))]
    weights += [(-1)**(k+1) * comb(n, k) * (scale // k)
                for k in range(1, n + 1)]
    # Verify differentiation weights on the entire monomial basis.
    for d in range(n + 1):
        got = sum(w * k**d for k, w in enumerate(weights))
        check(got == (scale if d == 1 else 0), 'Interpolation weights')
    base_value = evaluate(BASE)
    cols = []
    for i in range(45):
        numerator = [weights[0] * a for a in base_value] + [0] * (45 - len(base_value))
        for k in range(1, n + 1):
            theta = BASE.copy()
            theta[i] += k
            p = evaluate(theta)
            for j, a in enumerate(p):
                numerator[j] += weights[k] * a
        col = []
        for a in numerator:
            q, r = divmod(a, scale)
            check(r == 0, 'Nonintegral recovered derivative')
            col.append(q)
        cols.append(col)
    return [[cols[j][i] for j in range(45)] for i in range(45)]


def rational_det(matrix):
    # Ordinary Gaussian elimination over Q, not Bareiss elimination.
    a = [[Fraction(v) for v in row] for row in matrix]
    det = Fraction(1)
    pivots = []
    swaps = []
    n = len(a)
    for k in range(n):
        j = next((j for j in range(k, n) if a[j][k]), None)
        if j is None:
            return Fraction(0), pivots, swaps
        if j != k:
            a[k], a[j] = a[j], a[k]
            det = -det
            swaps.append([k,j])
        pivot = a[k][k]
        pivots.append(str(pivot))
        det *= pivot
        for i in range(k + 1, n):
            if a[i][k]:
                factor = a[i][k] / pivot
                a[i][k] = Fraction(0)
                for j in range(k + 1, n):
                    a[i][j] -= factor * a[k][j]
    return det, pivots, swaps


def modular_inverse(a, prime):
    n = len(a)
    b = [[v % prime for v in row] + [int(i == j) for j in range(n)]
         for i, row in enumerate(a)]
    for k in range(n):
        index = next((i for i in range(k,n) if b[i][k]), None)
        check(index is not None, 'Singular modular matrix')
        b[k], b[index] = b[index], b[k]
        inv = pow(b[k][k], -1, prime)
        b[k] = [(v * inv) % prime for v in b[k]]
        for i in range(n):
            if i != k and b[i][k]:
                scalar = b[i][k]
                b[i] = [(x - scalar*y) % prime for x,y in zip(b[i],b[k])]
    inverse = [row[n:] for row in b]
    # Direct multiplication, separate from the elimination algorithm.
    for i in range(n):
        for j in range(n):
            check(sum(a[i][k] * inverse[k][j] for k in range(n)) % prime == int(i == j),
                  'Modular inverse certificate failed')
    return inverse


def main():
    out = Path(__file__).resolve().parent
    matrix = interpolate_jacobian()
    determinant, pivots, swaps = rational_det(matrix)
    inverse3 = modular_inverse(matrix, 3)
    check(determinant == 256, 'Disagreement with claimed integer determinant')
    record = {
        'method': 'Whole-circuit evaluation and exact degree-13 interpolation; no differentiation code',
        'parameter_order': NAMES,
        'parameter_point': BASE,
        'coefficient_degree_bound_in_parameters': 13,
        'interpolation_nodes': list(range(14)),
        'integer_jacobian': matrix,
        'exact_determinant': int(determinant),
        'rational_elimination_pivots': pivots,
        'rational_elimination_row_swaps': swaps,
        'inverse_mod_3': inverse3,
        'direct_product_J_inverse_mod_3': 'identity (all 2025 entries checked)',
    }
    (out/'interpolation_certificate.json').write_text(json.dumps(record, indent=2)+'\n')
    print('45-parameter map constructed from circuit equations, without truncation.')
    print('Derivative weights checked on all monomials of degrees 0 through 13.')
    print('Jacobian recovered from whole-circuit evaluations, using integer arithmetic.')
    print('Rational Gaussian-elimination determinant:', determinant)
    print('Inverse modulo 3 constructed; all 2025 entries of J*inverse equal identity modulo 3.')
    print('Entry range:', min(map(min,matrix)), max(map(max,matrix)))
    print('All checks passed.')


if __name__ == '__main__':
    main()

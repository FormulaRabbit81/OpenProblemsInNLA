#!/usr/bin/env python3
"""Fresh dependency-free exact symbolic audit of the MF-14 border lemma.

No original code, stored matrix, symbolic algebra package, floating point, or
polynomial truncation is used. Python 3.9+ standard library only.
"""
from functools import lru_cache
from pathlib import Path
import json

NAMES = ('x', 'alpha', 'eta', 'a', 'b', 'lambda', 'gamma', 's')
ZERO_MONOMIAL = (0,) * len(NAMES)


class Poly:
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = value.terms
        elif isinstance(value, dict):
            self.terms = {m: c for m, c in value.items() if c}
        else:
            self.terms = {ZERO_MONOMIAL: value} if value else {}

    def __add__(self, other):
        terms = self.terms.copy()
        for m, c in Poly(other).terms.items():
            terms[m] = terms.get(m, 0) + c
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        terms = {}
        for m, c in self.terms.items():
            for n, d in Poly(other).terms.items():
                e = tuple(a+b for a, b in zip(m, n))
                terms[e] = terms.get(e, 0) + c*d
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, n):
        result = Poly(1)
        for _ in range(n):
            result = result*self
        return result

    def coefficient(self, name, power):
        index = NAMES.index(name)
        terms = {}
        for m, c in self.terms.items():
            if m[index] == power:
                e = list(m)
                e[index] = 0
                terms[tuple(e)] = c
        return Poly(terms)

    def substitute(self, mapping):
        indices = {NAMES.index(k): Poly(v) for k, v in mapping.items()}
        result = Poly(0)
        for m, c in self.terms.items():
            remaining = list(m)
            term = Poly(c)
            for i, p in indices.items():
                term *= p**m[i]
                remaining[i] = 0
            result += term*Poly({tuple(remaining): 1})
        return result

    def divide_power(self, name, power):
        index = NAMES.index(name)
        terms = {}
        for m, c in self.terms.items():
            if m[index] < power:
                raise ArithmeticError('Inexact monomial division')
            e = list(m)
            e[index] -= power
            terms[tuple(e)] = c
        return Poly(terms)

    def valuation(self, name):
        i = NAMES.index(name)
        return min((m[i] for m in self.terms), default=None)

    def degree(self, name):
        i = NAMES.index(name)
        return max((m[i] for m in self.terms), default=-1)

    def __bool__(self):
        return bool(self.terms)

    def __str__(self):
        if not self:
            return '0'
        parts = []
        for m, c in sorted(self.terms.items(), reverse=True):
            factors = [name if n == 1 else name+'^'+str(n)
                       for name, n in zip(NAMES, m) if n]
            parts.append(str(c) + ('*'+'*'.join(factors) if factors else ''))
        return ' + '.join(parts).replace('+ -', '- ')


def variable(name):
    m = list(ZERO_MONOMIAL)
    m[NAMES.index(name)] = 1
    return Poly({tuple(m): 1})


def require_equal(actual, expected, message):
    difference = actual - expected
    if difference:
        raise ArithmeticError(message + ': ' + str(difference))


def determinant(matrix):
    """Division-free Laplace recursion, expanding the sparsest remaining row."""
    n = len(matrix)
    @lru_cache(None)
    def recurse(rows, cols):
        if not rows:
            return Poly(1)
        row = min(rows, key=lambda r: sum(bool(matrix[r][c]) for c in cols))
        row_position = rows.index(row)
        new_rows = tuple(r for r in rows if r != row)
        result = Poly(0)
        for col_position, col in enumerate(cols):
            if matrix[row][col]:
                new_cols = tuple(c for c in cols if c != col)
                result += ((-1)**(row_position+col_position))*matrix[row][col]*recurse(new_rows, new_cols)
        return result
    return recurse(tuple(range(n)), tuple(range(n)))


def coefficient_matrix(polynomials, degrees):
    return [[p.coefficient('x', d) for p in polynomials] for d in degrees]


def main():
    x, alpha, eta, a, b, lam, gamma, s = map(variable, NAMES)
    Q = x**4 + alpha*x**3
    R = a*Q**2 + b*x**2*Q + x*Q + eta*x**3
    delta, g = b-2*a, b-a
    n = eta-1+alpha*g
    left_cleared = delta*(a*Q+g*x**2) + (delta-a*n)*x
    right_cleared = delta*(Q+x**2) + n*x
    require_equal(left_cleared*right_cleared-g*Q*delta**2-(delta-a*n)*n*x**2,
                  delta**2*R, 'Third-product identity')
    print('PASS: exact third-product identity after clearing denominator squared.')

    # Prove all low monomials are products or sums of products from V.
    # x^3 = x*x^2; x^4 = x^2*x^2; x^5 = x*Q-alpha*x^4;
    # x^6 = x^2*Q-alpha*x^5.
    low = [Poly(1), x, x**2, x*x**2, x**2*x**2]
    low.append(x*Q-alpha*low[4])
    low.append(x**2*Q-alpha*low[5])
    for j, p in enumerate(low):
        require_equal(p, x**j, 'Low product-span monomial')
    span_basis = low + [Q**2, x*R, x**2*R, Q*R, R**2]
    span_minor = determinant(coefficient_matrix(span_basis, [0,1,2,3,4,5,6,8,9,10,12,16]))
    require_equal(span_minor, a**5, 'Product-span basis determinant')
    print('PASS: 12-dimensional product span for a != 0; basis minor a^5.')

    v = Q+lam*x**2
    differential = [Poly(1), x, x**2, Q, R, x*v, x**2*v, Q*v,
                    x*R, x**2*R, Q*R, R**2]
    minor = determinant(coefficient_matrix(differential, [0,1,2,3,4,5,6,8,9,10,12,16]))
    expected = a**5*(lam-eta-alpha*lam*(b-a*lam))
    require_equal(minor, expected, 'Differential minor')
    specialized = minor.substitute({'a': s**2, 'b': gamma*s, 'lambda': eta+1})
    require_equal(specialized, s**10*(1-alpha*(eta+1)*(gamma*s-(eta+1)*s**2)),
                  'Specialized differential minor')
    print('PASS: exact differential minor a^5*(lambda-eta-alpha*lambda*(b-a*lambda)).')

    Rs = R.substitute({'a': s**2, 'b': gamma*s})
    fs = [x**2*Rs, Q**2, Q*Rs, Rs**2, x*Rs]
    upper = coefficient_matrix(fs, [7,8,9,10])
    cofactors = []
    for i in range(5):
        minor4 = [[row[j] for j in range(5) if j != i] for row in upper]
        cofactors.append((-1)**i*determinant(minor4))
    E = sum((c*f for c, f in zip(cofactors, fs)), Poly(0))
    print('PASS: constructed entire E_s polynomial by cofactor expansion; degree', E.degree('x'))
    for d in range(7, 11):
        require_equal(E.coefficient('x', d), Poly(0), 'Eliminated coefficient')
    tail = E-sum((E.coefficient('x', j)*x**j for j in range(7)), Poly(0))
    Z = -tail.divide_power('s', 4)
    require_equal(Z.substitute({'s': 0}), x**12+(3*alpha-4*gamma**2)*x**11,
                  'Polynomial degeneration limit')
    expected_orders = [4,4,5,6,7,7]
    orders = [E.coefficient('x', d).valuation('s') for d in range(11,17)]
    if orders != expected_orders:
        raise ArithmeticError('Wrong high-degree valuations: '+str(orders))
    print('PASS: coefficients 7--10 vanish; valuations 11--16:', orders)
    print('PASS: polynomial family Z_s has limit x^12+(3*alpha-4*gamma^2)*x^11.')

    # Compact factored certificates for every high-degree coefficient. These
    # formulas were reconstructed from the coefficients of QR_s and R_s^2.
    C = (-1-3*alpha*gamma*s
         +(-2*alpha**3+9*alpha**2*gamma**2-6*alpha*eta-2*eta*gamma**2)*s**2
         +(-4*alpha**4*gamma+3*alpha**3*gamma**3+12*alpha**2*eta*gamma)*s**3
         +(-8*alpha**6-4*alpha**5*gamma**2-10*alpha**4*eta)*s**4)
    D = 2*gamma+(3*alpha**2-alpha*gamma**2-eta)*s-8*alpha**3*gamma*s**2+9*alpha**5*s**3
    require_equal(cofactors[2], s**2*C, 'C cofactor formula')
    require_equal(cofactors[3], s**3*D, 'D cofactor formula')
    high_coefficients = {
        11: s**4*(3*alpha*C+D*(2*gamma+(6*alpha**2+2*eta+2*alpha*gamma**2)*s+2*alpha**3*gamma*s**2)),
        12: s**4*(C+s*D*(6*alpha+gamma**2+6*alpha**2*gamma*s+alpha**4*s**2)),
        13: s**5*D*(2+6*alpha*gamma*s+4*alpha**3*s**2),
        14: s**6*D*(2*gamma+6*alpha**2*s),
        15: 4*alpha*s**7*D,
        16: s**7*D,
    }
    for degree, formula in high_coefficients.items():
        require_equal(E.coefficient('x', degree), formula, 'Factored high-degree coefficient')
    print('PASS: compact C,D cofactor formulas reproduce every high-degree coefficient.')

    lower_limits = [x**j for j in range(7)]+[f.substitute({'s':0}) for f in fs[:4]]
    require_equal(determinant(coefficient_matrix(lower_limits, list(range(11)))), 1,
                  'Lower limiting basis')
    if any(p.degree('x') > 10 for p in lower_limits):
        raise ArithmeticError('Lower limiting basis degree')
    print('PASS: eleven lower limits form a degree-at-most-ten basis with determinant 1.')

    output = Path(__file__).parent
    record = {'method': 'Fresh division-free multivariate sparse polynomial arithmetic',
              'differential_minor': str(minor),
              'specialized_minor': str(specialized),
              'E_s_cofactors': [str(c) for c in cofactors],
              'E_s_coefficients': {str(j): str(E.coefficient('x', j)) for j in range(17)},
              'Z_s': str(Z),
              'high_degree_valuations': orders,
              'verdict': 'All exact algebraic checks passed'}
    (output/'symbolic_certificate.json').write_text(json.dumps(record, indent=2)+'\n')
    print('All independent symbolic checks passed.')


if __name__ == '__main__':
    main()

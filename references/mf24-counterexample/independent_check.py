#!/usr/bin/env python3
"""Independent MF-24 checks, written from the supplied four-page manuscript.

Exact checks use only Python's standard library. --numeric adds NumPy checks.
This is supporting evidence for the written audit, not a formal proof checker.
Run: python3 independent_check.py --numeric --pdf /path/to/proof.pdf
"""
import argparse
from collections import defaultdict
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import platform


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


# Sparse multivariate polynomials over the rationals. No symbolic dependency.
def const(n, value):
    return {(0,) * n: F(value)} if value else {}


def variable(n, index):
    exponent = [0] * n
    exponent[index] = 1
    return {tuple(exponent): F(1)}


def add(a, b):
    result = dict(a)
    for monomial, value in b.items():
        result[monomial] = result.get(monomial, F(0)) + value
    return {m: c for m, c in result.items() if c}


def scale(a, c):
    return {m: v * c for m, v in a.items() if v * c}


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    result = defaultdict(F)
    for ma, va in a.items():
        for mb, vb in b.items():
            result[tuple(x + y for x, y in zip(ma, mb))] += va * vb
    return {m: c for m, c in result.items() if c}


def mmul(a, b):
    result = []
    for row in a:
        output = []
        for j in range(len(b[0])):
            total = {}
            for k in range(len(b)):
                total = add(total, mul(row[k], b[k][j]))
            output.append(total)
        result.append(output)
    return result


def evaluate(p, values):
    total = F(0)
    for powers, coefficient in p.items():
        for value, exponent in zip(values, powers):
            coefficient *= value ** exponent
        total += coefficient
    return total


def symbolic_bridge():
    u, rho, a, b, p, q, r, s = [variable(8, j) for j in range(8)]
    one, zero = const(8, 1), {}
    P = [[p, q], [r, s]]
    def K(c):
        return [[add(u, c), scale(mul(rho, c), -1)], [one, zero]]
    R, S = mmul(P, K(a)), mmul(P, K(b))
    v = mmul(P, [[u], [one]])
    RS, SR = mmul(R, S), mmul(S, R)
    commutator = [[sub(RS[i][j], SR[i][j]) for j in range(2)] for i in range(2)]
    require(not mmul(commutator, v)[0][0], 'generic bridge scalar is not zero')
    trace = add(R[0][0], R[1][1])
    determinant = sub(mul(R[0][0], R[1][1]), mul(R[0][1], R[1][0]))
    square = mmul(R, R)
    for i in range(2):
        for j in range(2):
            residual = sub(square[i][j], mul(trace, R[i][j]))
            if i == j:
                residual = add(residual, determinant)
            require(not residual, 'generic Cayley-Hamilton residual')


def exponents(m, which):
    # Literal word concatenation, independent of the closed-form heights.
    motif = [1] + [0] * (m - 1)
    if which == 'X':
        return motif + [0] + motif + ([-1] + motif) * (m - 1)
    return motif + ([-1] + motif) * (m - 1) + [0] + motif


def heights(word):
    h = [0]
    for x in word:
        h.append(h[-1] + x)
    return h


def gram_polynomial(word, t):
    # Variables u = |z|^2 + eta and rho = |z|^2.
    u, rho = variable(2, 0), variable(2, 1)
    previous, current = const(2, 1), u
    for exponent in word:
        a = t ** (2 * exponent)
        previous, current = current, sub(mul(add(u, const(2, a)), current), scale(mul(rho, previous), a))
    return current


def determinant(matrix):
    a = [row[:] for row in matrix]
    answer = F(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            answer = -answer
        diagonal = a[j][j]
        answer *= diagonal
        for i in range(j + 1, len(a)):
            factor = a[i][j] / diagonal
            if factor:
                for k in range(j + 1, len(a)):
                    a[i][k] -= factor * a[j][k]
                a[i][j] = F(0)
    return answer


def direct_gram_determinant(word, t, z, eta):
    n = len(word) + 1
    w = [[F(0) for _ in range(n)] for _ in range(n)]
    for j in range(n):
        w[j][j] = -z
    for j, exponent in enumerate(word):
        w[j][j + 1] = t ** exponent
    gram = [[sum(w[k][i] * w[k][j] for k in range(n)) + (eta if i == j else 0)
             for j in range(n)] for i in range(n)]
    return determinant(gram)


def exact_checks():
    symbolic_bridge()
    counts = {'generic_symbolic_bridge_and_cayley_hamilton': 'PASS'}
    blocks_checked = 0
    for m in range(2, 101):
        n, D, k = (m + 1) ** 2, m + 2, m + 1
        hx, hy = heights(exponents(m, 'X')), heights(exponents(m, 'Y'))
        require(len(hx) == len(hy) == n, 'word length')
        for vertex in range(n):
            q, s = divmod(vertex, k)
            require(hx[vertex] == int(s >= 1) + int(q >= 1), 'X height formula')
            require(hy[vertex] == int(s >= 1) + int(q == m), 'Y height formula')
        require(all(hx[j * D] == 2 for j in range(1, m + 1)), 'numerator row')
        require(hy[-1] - hy[0] == 2, 'nonzero denominator')
        require(4 * (m - 1) <= m * m, 'four-fifths lower bound')
        for residue in range(D):
            a = hy[residue::D]
            L = len(a)
            require(L in (m, m + 1), 'residue size')
            require(a.count(0) <= 1 and a.count(2) <= 1, 'exceptional height counts')
            for t in (F(101, 100), F(3, 2), F(m)):
                usq = sum(t ** (-2 * h) for h in a[:-1])
                vsq = sum(t ** (2 * h) for h in a[1:])
                require(usq <= 1 + (L - 2) / t ** 2, 'left vector norm')
                require(vsq <= t ** 4 + (L - 2) * t ** 2, 'right vector norm')
                require(usq * vsq <= (t ** 2 + m - 1) ** 2, 'block norm bound')
            blocks_checked += 1
    counts['word_height_and_block_checks_m_2_through_100'] = blocks_checked
    poly_count = 0
    direct_count = 0
    for m in range(2, 7):
        for t in (F(3, 2), F(2), F(3)):
            wx, wy = exponents(m, 'X'), exponents(m, 'Y')
            px, py = gram_polynomial(wx, t), gram_polynomial(wy, t)
            require(px == py, 'full bivariate determinant identity')
            poly_count += 1
            if m <= 4:
                for z, eta in ((F(0), F(1, 3)), (F(1, 2), F(2)), (F(-2), F(3, 5))):
                    predicted = evaluate(px, (z * z + eta, z * z))
                    for word in (wx, wy):
                        require(direct_gram_determinant(word, t, z, eta) == predicted,
                                'direct dense Gram determinant mismatch')
                        direct_count += 1
    counts['full_bivariate_determinant_identities'] = poly_count
    counts['independent_dense_gram_determinants_real_shifts'] = direct_count
    wrong = exponents(3, 'Y')
    wrong[0], wrong[2] = wrong[2], wrong[0]
    require(gram_polynomial(wrong, F(2)) != gram_polynomial(exponents(3, 'X'), F(2)),
            'incorrect-motif negative control was not rejected')
    counts['incorrect_motif_negative_control'] = 'REJECTED as expected'
    return counts


def numerical_checks():
    import numpy as np
    def shift(word, t):
        return np.diag(np.power(float(t), word), 1)
    comparisons, polynomial_pairs, max_scaled_error = 0, 0, 0.0
    rng = np.random.default_rng(240915)
    for m in range(2, 9):
        D, n = m + 2, (m + 1) ** 2
        for t in (1.01, 1.5, 2., float(m)):
            X, Y = [shift(exponents(m, name), t) for name in ('X', 'Y')]
            zvalues = [0, 1, -1, 1j, 1+2j] + list(rng.normal(size=5) + 1j * rng.normal(size=5))
            for z in zvalues:
                sx, sy = [np.linalg.svd(W - z * np.eye(n), compute_uv=False) for W in (X, Y)]
                error = float(np.max(np.abs(sx-sy)) / max(1., float(sx[0]), float(sy[0])))
                max_scaled_error = max(max_scaled_error, error)
                require(error < 2e-13, 'complex shifted SVD check')
                comparisons += 1
            polys = []
            for W in (X, Y):
                WD = np.linalg.matrix_power(W, D)
                power, pW = np.eye(n), np.zeros((n, n))
                for _ in range(m):
                    power = power @ WD
                    pW += power
                polys.append(pW)
            pX, pY = polys
            nx, ny = [float(np.linalg.norm(P, 2)) for P in polys]
            require(nx + 1e-10 >= t*t*np.sqrt(m), 'numerator norm')
            require(ny <= t*t + m - 1 + 1e-10, 'denominator norm')
            require(ny > 0, 'denominator vanishes')
            hy = heights(exponents(m, 'Y'))
            for row in range(n):
                for col in range(n):
                    expected = t ** (hy[col] - hy[row]) if col > row and (col-row) % D == 0 else 0
                    require(abs(pY[row, col] - expected) < 1e-9, 'direct polynomial/residue entry')
            polynomial_pairs += 1
    rows = []
    for m in (2, 3, 4, 9, 19, 49):
        n, D, t = (m + 1) ** 2, m + 2, float(m)
        norms = []
        for name in ('X', 'Y'):
            h = heights(exponents(m, name))
            block_norms = []
            for residue in range(D):
                a = np.asarray(h[residue::D])
                block = np.triu(t ** (a[None, :] - a[:, None]), 1)
                block_norms.append(float(np.linalg.norm(block, 2)))
            norms.append(max(block_norms))
        rows.append({'m':m, 'N':n, 'ratio':norms[0]/norms[1],
                     'proved_lower_bound':m**0.5/(1+(m-1)/m**2)})
    return {'numpy': np.__version__, 'complex_shifted_svd_comparisons': comparisons,
            'max_error_divided_by_max_1_largest_singular_value':max_scaled_error,
            'dense_polynomial_pairs_and_residue_comparisons':polynomial_pairs,
            'ratios_from_residue_blocks':rows,
            'limitation':'Floating-point diagnostics do not prove exact equality or relative accuracy of small singular values.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--numeric', action='store_true')
    parser.add_argument('--pdf', type=Path)
    args = parser.parse_args()
    report = {'started_utc':datetime.now(timezone.utc).isoformat(), 'python':platform.python_version(),
              'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    if args.pdf:
        report['pdf_sha256'] = hashlib.sha256(args.pdf.read_bytes()).hexdigest()
    report['exact'] = exact_checks()
    if args.numeric:
        report['numeric'] = numerical_checks()
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    report['result'] = 'PASS'
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

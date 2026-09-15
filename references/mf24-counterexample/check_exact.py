"""Exact supporting identities and finite counterexample checks for proof.pdf.

Run: python check_exact.py
Requires SymPy and NumPy. No floating-point comparison is used below.
"""

from fractions import Fraction
from math import isqrt, prod

import sympy as sp

from mf24 import exponents, heights


def require(condition: bool, message: str) -> None:
    """Unlike assert, this check is not disabled by python -O."""
    if not condition:
        raise AssertionError(message)


def weights(m: int, t: Fraction, side: str) -> list[Fraction]:
    """Independent edge-by-edge construction, without motif concatenation."""
    k = m + 1
    exceptional = 1 if side == "X" else m
    result = []
    for edge in range(1, k * k):
        if edge % k == 1:
            result.append(t)
        elif edge % k == 0 and edge // k != exceptional:
            result.append(1 / t)
        else:
            result.append(Fraction(1))
    return result


def continuant(word: list[Fraction]) -> sp.Poly:
    """det((W-zI)^* (W-zI) + eta I), in u=eta+|z|^2 and rho=|z|^2."""
    u, rho = sp.symbols("u rho")
    previous = sp.Poly(1, u, rho, domain=sp.QQ)
    current = sp.Poly(u, u, rho, domain=sp.QQ)
    for weight in word:
        a = sp.Rational(weight**2)
        previous, current = current, (u + a) * current - rho * a * previous
    return current


def direct_polynomial(word: list[Fraction], m: int) -> sp.Matrix:
    """Evaluate p_m(W) by matrix powers, not by prefix heights."""
    n = len(word) + 1
    w = sp.zeros(n)
    for i, weight in enumerate(word):
        w[i, i + 1] = sp.Rational(weight)
    step = w ** (m + 2)
    power = sp.eye(n)
    result = sp.zeros(n)
    for _ in range(m):
        power = power * step
        result += power
    return result


def path_blocks(word: list[Fraction], m: int) -> list[sp.Matrix]:
    """Residue blocks obtained from direct products of the actual weights."""
    blocks = []
    for residue in range(m + 2):
        vertices = list(range(residue, len(word) + 1, m + 2))
        block = sp.zeros(len(vertices))
        for i, start in enumerate(vertices):
            for j in range(i + 1, len(vertices)):
                block[i, j] = sp.Rational(prod(word[start:vertices[j]]))
        blocks.append(block)
    return blocks


def positive_ldl(matrix: sp.Matrix) -> None:
    """Verify a rational LDL^T factorization with strictly positive pivots."""
    n = matrix.rows
    require(matrix == matrix.T, "LDL input is not symmetric")
    lower = sp.eye(n)
    diagonal = []
    for j in range(n):
        pivot = matrix[j, j] - sum(lower[j, k]**2 * diagonal[k]
                                  for k in range(j))
        require(pivot > 0, "LDL pivot is not strictly positive")
        diagonal.append(pivot)
        for i in range(j + 1, n):
            lower[i, j] = (matrix[i, j]
                           - sum(lower[i, k] * lower[j, k] * diagonal[k]
                                 for k in range(j))) / pivot
    require(lower * sp.diag(*diagonal) * lower.T == matrix,
            "LDL reconstruction failed")


def check_bridge_identity() -> None:
    u, rho, a, b, p, q, r, s = sp.symbols("u rho a b p q r s")
    p_matrix = sp.Matrix([[p, q], [r, s]])
    v = p_matrix * sp.Matrix([u, 1])
    f = sp.Matrix([[1, 0]])

    def k(c):
        return sp.Matrix([[u + c, -rho * c], [1, 0]])

    left, right = p_matrix * k(a), p_matrix * k(b)
    scalar = (f * (left * right - right * left) * v)[0]
    require(sp.expand(scalar) == 0, "sandwiched commutator identity failed")
    cayley_hamilton = left**2 - sp.trace(left) * left + left.det() * sp.eye(2)
    require(cayley_hamilton.applyfunc(sp.expand) == sp.zeros(2),
            "Cayley-Hamilton identity failed")
    print("PASS: generic bridge commutator and Cayley-Hamilton identities")


def check_words_and_heights() -> None:
    for m in range(2, 31):
        k = m + 1
        for side in ("X", "Y"):
            word = weights(m, Fraction(3, 2), side)
            require(word == [Fraction(3, 2)**e for e in exponents(m, side)],
                    f"two constructions differ: m={m}, side={side}")
            h = heights(m, side)
            require(len(h) == k * k, "wrong number of vertices")
            for vertex, height in enumerate(h):
                q, s = divmod(vertex, k)
                raised = (q >= 1) if side == "X" else (q == m)
                require(height == int(s >= 1) + int(raised),
                        "closed prefix-height formula failed")
            if side == "Y":
                for residue in range(m + 2):
                    block_heights = h[residue::m + 2]
                    require(len(block_heights) in (m, m + 1), "wrong block size")
                    require(block_heights.count(0) <= 1, "repeated height zero")
                    require(block_heights.count(2) <= 1, "repeated height two")
    print("PASS: independent words, prefix heights and residue sizes, m=2,...,30")


def check_determinants() -> None:
    u, rho, eta = sp.symbols("u rho eta")
    count = 0
    for m in range(2, 8):
        for t in (Fraction(2), Fraction(3, 2), Fraction(7, 5)):
            require(continuant(weights(m, t, "X"))
                    == continuant(weights(m, t, "Y")),
                    f"bivariate determinant mismatch: m={m}, t={t}")
            count += 1
    print(f"PASS: {count} full bivariate determinant identities")

    # Keep z and its conjugate independent: this checks all complex shifts,
    # not a grid of particular shifts, for these finite-dimensional examples.
    z, zbar = sp.symbols("z zbar")
    count = 0
    for m in (2, 3, 4):
        for side in ("X", "Y"):
            word = weights(m, Fraction(3, 2), side)
            n = len(word) + 1
            w = sp.zeros(n)
            for i, weight in enumerate(word):
                w[i, i + 1] = sp.Rational(weight)
            shifted = w - z * sp.eye(n)
            gram = (shifted.conjugate().T * shifted).subs(sp.conjugate(z), zbar)
            gram = gram.applyfunc(sp.expand)
            direct = (-gram).charpoly(eta).as_expr()
            recurrence = continuant(word).as_expr().subs(
                {u: eta + z * zbar, rho: z * zbar})
            require(sp.Poly(direct - recurrence, eta, z, zbar).is_zero,
                    "Gram characteristic polynomial disagrees with recurrence")
            count += 1
    print(f"PASS: {count} direct Gram identities with eta, z and zbar symbolic")


def check_polynomials_and_norms() -> None:
    for m in (2, 3, 4):
        for side in ("X", "Y"):
            word = weights(m, Fraction(3, 2), side)
            p = direct_polynomial(word, m)
            vertices = [i for residue in range(m + 2)
                        for i in range(residue, len(word) + 1, m + 2)]
            permuted = p.extract(vertices, vertices)
            require(permuted == sp.diag(*path_blocks(word, m)),
                    "matrix-power polynomial disagrees with path blocks")
    print("PASS: 6 direct polynomial-matrix evaluations and block decompositions")

    for m in (4, 9):
        t = Fraction(m)
        x = weights(m, t, "X")
        y = weights(m, t, "Y")
        require(continuant(x) == continuant(y),
                "certificate pair has different shifted Gram polynomials")
        row_squared = sum(prod(x[:j * (m + 2)])**2 for j in range(1, m + 1))
        require(row_squared == t**4 * m, "numerator row norm failed")
        bound = t**2 + m - 1
        for block in path_blocks(y, m):
            positive_ldl(bound**2 * sp.eye(block.cols) - block.T * block)
        root_m = isqrt(m)
        require(root_m**2 == m, "certificate examples need a square m")
        numerator = int(t**2) * root_m
        print(f"PASS: exact rational counterexample certificate, "
              f"m=t={m}, ratio > {numerator}/{bound}")


def check_negative_controls() -> None:
    m = 4
    correct = weights(m, Fraction(4), "Y")
    wrong = correct.copy()
    # Move the exceptional bridge one position inward, preserving all weights.
    i, j = (m - 1) * (m + 1) - 1, m * (m + 1) - 1
    wrong[i], wrong[j] = wrong[j], wrong[i]
    require(sorted(wrong) == sorted(correct), "control changed the weight multiset")
    require(continuant(wrong) != continuant(correct),
            "determinant test missed the misplaced bridge")
    try:
        positive_ldl(sp.diag(1, 0))
    except AssertionError:
        pass
    else:
        raise AssertionError("LDL test accepted a non-positive-definite matrix")
    print("PASS: a misplaced bridge and a zero LDL pivot are both rejected")


def main() -> None:
    check_bridge_identity()
    check_words_and_heights()
    check_determinants()
    check_polynomials_and_norms()
    check_negative_controls()
    print("All exact checks passed. This is not an end-to-end formal proof.")


if __name__ == "__main__":
    main()

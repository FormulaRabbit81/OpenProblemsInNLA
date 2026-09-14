"""Exact tools for the fourth AC-06 research report.

No function in this module is a polynomial-time quadratic-border-rank selector.
The compactor preserves bounded polynomial certificates *when* a supplied list
contains a point detected by one. It does not check that premise.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, gcd, isqrt, prod
from typing import Mapping, Sequence

Exponent = tuple[int, ...]
Polynomial = Mapping[Exponent, int]


def _integer(value: int, name: str, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def evaluate(polynomial: Polynomial, point: Sequence[int | Fraction]) -> int | Fraction:
    """Evaluate an explicitly stored polynomial using exact arithmetic."""
    total: int | Fraction = 0
    for exponent, coefficient in polynomial.items():
        if len(exponent) != len(point) or any(e < 0 for e in exponent):
            raise ValueError("invalid exponent")
        term: int | Fraction = coefficient
        for x, e in zip(point, exponent):
            term *= x ** e
        total += term
    return total


def monomials(variables: int, degree: int) -> list[Exponent]:
    _integer(variables, "variables", 1)
    _integer(degree, "degree")
    if comb(variables + degree, variables) > 100_000:
        raise ValueError("explicit monomial-list allocation guard")
    def generate(prefix: tuple[int, ...], left: int, count: int):
        if count == 0:
            yield prefix
        else:
            for e in range(left + 1):
                yield from generate(prefix + (e,), left - e, count - 1)
    return list(generate((), degree, variables))


def _candidate_data(points: Sequence[Sequence[int]]) -> tuple[list[list[int]], int, int, int]:
    if not points or not points[0]:
        raise ValueError("supply a nonempty list of nonempty points")
    data = [list(row) for row in points]
    n = len(data[0])
    if any(len(row) != n for row in data):
        raise ValueError("candidate dimensions must agree")
    if any(isinstance(v, bool) or not isinstance(v, int) for row in data for v in row):
        raise ValueError("integer candidates required; use compact_rational for Fractions")
    return data, n, len(data), max(1, max(abs(v) for row in data for v in row))


def compact_list(points: Sequence[Sequence[int]], degree: int, height: int = 1,
                 max_output_bits: int = 2_000_000) -> dict:
    """Merge an integer list into an integer point preserving small certificates.

    For every integer P with total degree <= degree and coefficient magnitude
    <= height, P nonzero at any input implies P nonzero at the output. The
    function does not receive P. Its degree/height parameters are promises about
    possible certificates, not a certificate that an input tensor has high rank.
    """
    degree = _integer(degree, "degree")
    height = _integer(height, "height", 1)
    _integer(max_output_bits, "max_output_bits", 1)
    data, n, length, alphabet = _candidate_data(points)
    if length > 2000 or n > 100_000 or degree > 1_000_000:
        raise ValueError("demonstration allocation guard")
    if length == 1:
        return {"point": data[0].copy(), "base": 1,
                "common_denominator": 1, "coefficient_bound": None,
                "guarantee": "BOUNDED_CERTIFICATE_PRESERVATION_ONLY",
                "list_length": 1, "variables": n}
    u = comb(n + degree, n)
    denominator = factorial(length - 1)
    c = alphabet * (1 << (length - 1)) * factorial(length)
    base_bits_upper = max(length.bit_length(),
                         1 + u.bit_length() + height.bit_length() + degree * c.bit_length())
    output_bits_upper = n * (3 + c.bit_length() + (length - 1) * base_bits_upper
                             + denominator.bit_length())
    if output_bits_upper > max_output_bits:
        raise ValueError(f"estimated output exceeds guard: {output_bits_upper} bits")
    coefficient_bound = u * height * c ** degree
    base = max(length, coefficient_bound + 1)
    # base >= length, so all the following denominators are nonzero.
    common_product = prod(base - j for j in range(length))
    interpolation_weights = [((-1) ** (length - 1 - j)) * comb(length - 1, j)
                             * (common_product // (base - j))
                             for j in range(length)]
    numerators = [sum(interpolation_weights[j] * data[j][i]
                      for j in range(length)) for i in range(n)]
    # Consecutive-node Lagrange polynomials are integer-valued at integer B.
    if any(v % denominator for v in numerators):
        raise ArithmeticError("integer-valued interpolation invariant failed")
    output = [v // denominator for v in numerators]
    return {"point": output, "base": base, "common_denominator": denominator,
            "coefficient_bound": coefficient_bound, "coefficient_l1_bound": c,
            "monomial_count_bound": u, "output_bits_upper": output_bits_upper,
            "guarantee": "BOUNDED_CERTIFICATE_PRESERVATION_ONLY",
            "list_length": length, "variables": n}


def compact_rational(points: Sequence[Sequence[Fraction | int]], degree: int,
                     height: int = 1, max_output_bits: int = 2_000_000) -> dict:
    """Rational-input version, with explicit denominator and height clearing."""
    if not points or not points[0]:
        raise ValueError("nonempty input required")
    if any(not isinstance(v, (int, Fraction)) or isinstance(v, bool)
           for row in points for v in row):
        raise ValueError("use int or Fraction, never floating point")
    degree = _integer(degree, "degree")
    height = _integer(height, "height", 1)
    rational = [[Fraction(v) for v in row] for row in points]
    denominator = 1
    for row in rational:
        for value in row:
            denominator = denominator * value.denominator // gcd(denominator, value.denominator)
    if degree * denominator.bit_length() > max_output_bits:
        raise ValueError("denominator-clearing allocation guard")
    integers = [[int(v * denominator) for v in row] for row in rational]
    result = compact_list(integers, degree, height * denominator ** degree, max_output_bits)
    result["point"] = [Fraction(v, denominator) for v in result["point"]]
    result["input_denominator"] = denominator
    return result


def compact_crt(points: Sequence[Sequence[int]], degree: int, height: int = 1,
                max_output_bits: int = 2_000_000) -> dict:
    """Integer-output alternative. No large-prime search is required."""
    data, n, length, alphabet = _candidate_data(points)
    degree = _integer(degree, "degree")
    height = _integer(height, "height", 1)
    if length > 2000 or n > 100_000 or degree > 1_000_000:
        raise ValueError("demonstration allocation guard")
    _integer(max_output_bits, "max_output_bits", 1)
    u = comb(n + degree, n)
    if degree * alphabet.bit_length() > max_output_bits:
        raise ValueError("CRT evaluation-bound allocation guard")
    bound = u * height * alphabet ** degree
    exponent = bound.bit_length()
    fac = factorial(length)
    bases = [1 + j * fac for j in range(1, length + 1)]
    bit_upper = n * exponent * sum(a.bit_length() for a in bases)
    if bit_upper > max_output_bits:
        raise ValueError("CRT output exceeds demonstration allocation guard")
    moduli = [a ** exponent for a in bases]
    modulus = prod(moduli)
    weights = []
    for m in moduli:
        quotient = modulus // m
        weights.append((quotient * pow(quotient, -1, m)) % modulus)
    output = [sum(weights[j] * data[j][i] for j in range(length)) % modulus
              for i in range(n)]
    return {"point": output, "moduli": moduli, "modulus": modulus,
            "evaluation_bound": bound, "exponent": exponent,
            "guarantee": "BOUNDED_CERTIFICATE_PRESERVATION_ONLY"}


def specialize_monomial_curve(weights: Sequence[int], degree: int, height: int = 1,
                               max_output_bits: int = 2_000_000) -> dict:
    """Specialize a monomial curve, preserving every nonzero bounded pullback.

    The condition P(t**weights) != 0 as a polynomial is not tested here.
    """
    degree = _integer(degree, "degree")
    height = _integer(height, "height", 1)
    if not weights:
        raise ValueError("nonempty weight vector required")
    for w in weights:
        _integer(w, "weight")
    u = comb(len(weights) + degree, len(weights))
    base = 1 + u * height
    if sum(1 + w * base.bit_length() for w in weights) > max_output_bits:
        raise ValueError("curve output exceeds demonstration allocation guard")
    return {"point": [base ** w for w in weights], "base": base,
            "guarantee": "NONZERO_BOUNDED_PULLBACK_PRESERVATION_ONLY"}


def substitute_weights(polynomial: Polynomial, weights: Sequence[int]) -> dict[int, int]:
    answer: dict[int, int] = {}
    for alpha, coefficient in polynomial.items():
        if len(alpha) != len(weights):
            raise ValueError("dimension mismatch")
        exponent = sum(a * w for a, w in zip(alpha, weights))
        answer[exponent] = answer.get(exponent, 0) + coefficient
    return {exponent: coefficient for exponent, coefficient in answer.items() if coefficient}


def kronecker_koszul_data(n: int, partitions: Sequence[Sequence[Sequence[int]]],
                          shifts: Sequence[Sequence[int]]) -> dict:
    """Dimensions and a ceiling for the *published coloring-count criterion*.

    This is not a ceiling for border rank itself or for sharpened methods.
    """
    _integer(n, "n", 1)
    if len(partitions) != 3 or len(shifts) != 3:
        raise ValueError("three mode partitions and shift lists required")
    if not partitions[0]:
        raise ValueError("partitions must be nonempty")
    first = [v for block in partitions[0] for v in block]
    k = len(first)
    if sorted(first) != list(range(k)):
        raise ValueError("each partition must cover 0,...,k-1 exactly once")
    edges: set[tuple[int, int]] = set()
    dimensions: list[int] = []
    cost = 1
    binomial_product = 1
    for partition, ds in zip(partitions, shifts):
        if len(partition) != len(ds) or sorted(v for b in partition for v in b) != list(range(k)):
            raise ValueError("invalid partition or shift list")
        for block, p in zip(partition, ds):
            _integer(p, "shift")
            t = len(block)
            if not t or p + t > n:
                raise ValueError("zero-dimensional exterior factor or empty block")
            dimensions += [comb(n, p + t), comb(n, p)]
            cost *= comb(n - t, p)
            binomial_product *= comb(n, t)
            edges.update(tuple(sorted(pair)) for pair in combinations(block, 2))
    degrees = [0] * k
    for a, b in edges:
        degrees[a] += 1
        degrees[b] += 1
    delta = max(degrees, default=0)
    dimension_product = prod(dimensions)
    root = isqrt(n ** 3)
    if root * root < n ** 3:
        root += 1
    # Smallest integer x with x^(2k) * cost^2 >= the product of matrix-side dimensions.
    lo, hi = 0, max(1, root)
    while lo + 1 < hi:
        middle = (lo + hi) // 2
        if middle ** (2 * k) * cost * cost >= dimension_product:
            hi = middle
        else:
            lo = middle
    return {"n": n, "power": k, "dimensions": dimensions, "rank_cost": cost,
            "dimension_product": dimension_product, "binomial_product": binomial_product,
            "edges": sorted(edges), "maximum_degree": delta,
            "dimension_pattern_ceiling": delta + hi,
            "linear_iteration_pattern_ceiling": delta + 8*n,
            "pattern_ceiling": delta + min(hi, 8*n),
            "elementary_uniform_ceiling": root + 3 * (n - 1),
            "linear_iteration_uniform_ceiling": 11*n - 3,
            "uniform_ceiling": min(root + 3 * (n - 1), 11*n - 3),
            "scope": "COLORING_COUNT_THRESHOLD_ONLY"}


def count_colorings(k: int, edges: Sequence[tuple[int, int]], colors: int) -> int:
    _integer(k, "k")
    _integer(colors, "colors")
    if k > 8 or colors ** k > 2_000_000:
        raise ValueError("color enumeration guard")
    prior = [[] for _ in range(k)]
    for a, b in edges:
        a, b = sorted((a, b))
        prior[b].append(a)
    assignment = [-1] * k
    def go(v: int) -> int:
        if v == k:
            return 1
        forbidden = {assignment[u] for u in prior[v]}
        answer = 0
        for color in range(colors):
            if color not in forbidden:
                assignment[v] = color
                answer += go(v + 1)
        return answer
    return go(0)


def shifted_weights(n: int) -> list[int]:
    _integer(n, "n", 1)
    m = n * n
    return [m * (i*j + i*k + j*k) + i*j*k
            for k in range(n) for j in range(n) for i in range(n)]


def koszul_matrix_mod(n: int, p: int, prime: int, weights: Sequence[int]):
    """Integer Koszul flattening reduced modulo a prime, no floating point."""
    import numpy as np
    _integer(n, "n", 1)
    _integer(p, "p")
    _integer(prime, "prime", 2)
    if not 0 <= p < n or len(weights) != n ** 3:
        raise ValueError("invalid Koszul dimensions")
    if prime < 2 or prime > 1_000_000:
        raise ValueError("small prime required for safe exact int64 arithmetic")
    if any(prime % d == 0 for d in range(2, isqrt(prime) + 1)):
        raise ValueError("modulus must be prime")
    domain = list(combinations(range(n), p))
    codomain = list(combinations(range(n), p + 1))
    row_index = {s: i for i, s in enumerate(codomain)}
    if n*n*len(domain)*len(codomain) > 2_000_000:
        raise ValueError("matrix allocation guard")
    matrix = np.zeros((n * len(codomain), n * len(domain)), dtype=np.int64)
    for w in weights:
        _integer(w, "weight")
    tensor = [pow(2, w, prime) for w in weights]
    for column_block, subset in enumerate(domain):
        for i in range(n):
            if i in subset:
                continue
            union = tuple(sorted(subset + (i,)))
            row_block = row_index[union]
            sign = -1 if sum(s < i for s in subset) % 2 else 1
            for j in range(n):
                for k in range(n):
                    matrix[row_block*n+k, column_block*n+j] = sign * tensor[i+n*j+n*n*k] % prime
    return matrix


def modular_rank_certificate(matrix, prime: int) -> dict:
    """Rank and a nonsingular-minor certificate over a prime field."""
    import numpy as np
    _integer(prime, "prime", 2)
    if prime > 1_000_000 or any(prime % d == 0 for d in range(2, isqrt(prime) + 1)):
        raise ValueError("prime at most one million required for exact int64 arithmetic")
    raw = np.asarray(matrix)
    if raw.ndim != 2 or raw.dtype.kind not in "iu":
        raise ValueError("a two-dimensional integer array is required")
    if raw.dtype.kind == "u" and raw.size and int(raw.max()) > (1 << 63) - 1:
        raise ValueError("integer inputs must fit signed int64")
    work = np.array(raw, dtype=np.int64, copy=True) % prime
    rows, columns = work.shape
    row_ids = list(range(rows))
    pivot_columns: list[int] = []
    rank = 0
    for column in range(columns):
        candidates = np.flatnonzero(work[rank:, column])
        if not len(candidates):
            continue
        pivot = rank + int(candidates[0])
        if pivot != rank:
            work[[rank, pivot]] = work[[pivot, rank]]
            row_ids[rank], row_ids[pivot] = row_ids[pivot], row_ids[rank]
        inverse = pow(int(work[rank, column]), -1, prime)
        work[rank, column:] = (work[rank, column:] * inverse) % prime
        nonzero = np.flatnonzero(work[rank+1:, column]) + rank + 1
        if len(nonzero):
            factors = work[nonzero, column].copy()
            work[nonzero, column:] = (work[nonzero, column:] - factors[:, None]
                                      * work[rank, column:][None, :]) % prime
        pivot_columns.append(column)
        rank += 1
        if rank == rows:
            break
    return {"rank_mod_prime": rank, "prime": prime,
            "minor_rows": row_ids[:rank], "minor_columns": pivot_columns}


def shifted_certificate(n: int, prime: int = 65521) -> dict:
    p = (n - 1) // 2
    matrix = koszul_matrix_mod(n, p, prime, shifted_weights(n))
    result = modular_rank_certificate(matrix, prime)
    pure_cost = comb(n - 1, p)
    result.update({"n": n, "exterior_degree": p, "matrix_shape": list(matrix.shape),
                   "pure_tensor_rank_bound": pure_cost,
                   "certified_border_rank_lower_bound": (result["rank_mod_prime"] + pure_cost - 1) // pure_cost,
                   "scope": "FINITE_EXACT_MODULAR_LOWER_BOUND_NOT_QUADRATIC_FAMILY_PROOF"})
    return result


def _json_default(value):
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    raise TypeError(type(value).__name__)


def main() -> None:
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    compact = sub.add_parser("compact-demo")
    compact.add_argument("--integer-output", action="store_true")
    curve = sub.add_parser("curve-demo")
    finite = sub.add_parser("shifted-certificate")
    finite.add_argument("n", type=int)
    finite.add_argument("--prime", type=int, default=65521)
    ceiling = sub.add_parser("ceiling")
    ceiling.add_argument("n", type=int)
    args = parser.parse_args()
    if args.command == "compact-demo":
        points = [[0, 0], [1, 0], [0, 1]]
        out = compact_crt(points, 2) if args.integer_output else compact_list(points, 2)
    elif args.command == "curve-demo":
        out = specialize_monomial_curve([0, 0, 0, 1, 0, 0, 0, 0], 2)
    elif args.command == "shifted-certificate":
        out = shifted_certificate(args.n, args.prime)
    else:
        _integer(args.n, "n", 1)
        root = isqrt(args.n ** 3)
        elementary = root + (root*root < args.n**3) + 3*(args.n-1)
        out = {"n": args.n, "elementary_ceiling": elementary,
               "linear_iteration_ceiling": 11*args.n - 3,
               "coloring_criterion_ceiling": min(elementary, 11*args.n - 3),
               "scope": "NOT_A_BORDER_RANK_UPPER_BOUND"}
    print(json.dumps(out, indent=2, default=_json_default))


if __name__ == "__main__":
    main()

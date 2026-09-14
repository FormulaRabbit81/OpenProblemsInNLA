#!/usr/bin/env python3
"""Exact rational certificates for the AC-04 upper-bound refinement.

Only the Python standard library is used.  No floating-point comparisons enter
any certificate.  The accompanying report supplies the mathematical argument
linking these scalar inequalities to asymptotic tensor rank.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as F
import json
from pathlib import Path


def icbrt(n: int) -> int:
    """Return floor(n**(1/3)) by integer comparisons, for n >= 0."""
    if n < 0:
        raise ValueError("icbrt requires a nonnegative integer")
    if n < 2:
        return n
    lo, hi = 0, 1 << ((n.bit_length() + 2) // 3)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid <= n:
            lo = mid
        else:
            hi = mid
    assert lo**3 <= n < (lo + 1)**3
    return lo


@dataclass(frozen=True)
class Interval:
    """Closed rational interval, with exact (unrounded) endpoint arithmetic."""
    lo: F
    hi: F

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("Reversed interval")

    @staticmethod
    def exact(x: F | int) -> 'Interval':
        return Interval(F(x), F(x))

    def __add__(self, other: 'Interval') -> 'Interval':
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other: 'Interval') -> 'Interval':
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def square(self) -> 'Interval':
        if self.lo >= 0:
            return Interval(self.lo**2, self.hi**2)
        if self.hi <= 0:
            return Interval(self.hi**2, self.lo**2)
        return Interval(F(0), max(self.lo**2, self.hi**2))

    def div_positive(self, x: F | int) -> 'Interval':
        x = F(x)
        if x <= 0:
            raise ValueError("Divisor must be positive")
        return Interval(self.lo / x, self.hi / x)

    def as_json(self) -> dict[str, str]:
        return {"lower_rational": str(self.lo), "upper_rational": str(self.hi),
                "lower_decimal_for_display": decimal(self.lo),
                "upper_decimal_for_display": decimal(self.hi)}


def decimal(x: F, precision: int = 35) -> str:
    """Decimal display only; certificate decisions never use this function."""
    with localcontext() as ctx:
        ctx.prec = precision
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def cbrt_interval(x: int, digits: int = 40) -> Interval:
    """Enclose the real cube root of integer x >= 0 by exact rationals."""
    if x < 0 or digits < 0:
        raise ValueError("Require x >= 0 and digits >= 0")
    scale = 10**digits
    target = x * scale**3
    a = icbrt(target)
    if a**3 == target:
        return Interval.exact(F(a, scale))
    result = Interval(F(a, scale), F(a + 1, scale))
    assert result.lo**3 < x < result.hi**3
    return result


def pow_two_thirds(t: int, digits: int = 40) -> Interval:
    return cbrt_interval(t * t, digits)


def dimensions(n: int, steps: int) -> list[tuple[int, int, int]]:
    """(nonslice dimension, distinguished slice size, source dimension)."""
    if n < 3 or steps < 0:
        raise ValueError("This certificate uses n >= 3 and steps >= 0")
    M, d = 4**n + 2**n, 3**n
    t = M - 2 * d
    result = [(d, t, M)]
    M0, delta0 = M, M - 3 * d
    for j in range(steps):
        d, t, M = d*d + 2*d*t, t*t + 2*d*d, M*M
        assert M == t + 2*d
        assert d == (M0**(2**(j+1)) - delta0**(2**(j+1))) // 3
        assert t == (M0**(2**(j+1)) + 2*delta0**(2**(j+1))) // 3
        result.append((d, t, M))
    return result


def normalized_p(alpha: F, steps: int, n: int = 3,
                 digits: int = 40) -> Interval:
    """p_steps(alpha**n, 2/3) / (4**n + (2**n)**(2/3))**(2**steps).

    For n=3 or n=6 the denominator is rational. The delivered certificate uses
    n=3. Other n need interval division and are intentionally not supported.
    """
    if n % 3 != 0:
        raise ValueError("For exact denominator, n must be divisible by 3")
    rows = dimensions(n, steps)
    p = Interval.exact(alpha**n) + pow_two_thirds(rows[0][1], digits)
    for j in range(steps):
        tj, tn = rows[j][1], rows[j+1][1]
        p = p.square() - pow_two_thirds(tj, digits).square() + pow_two_thirds(tn, digits)
        assert p.lo > 0
    h = 4**n + 2**(2*n//3)
    return p.div_positive(h**(2**steps))


def certify() -> dict:
    rows = dimensions(3, 5)
    alpha = F("3.923038")
    upper_check = normalized_p(alpha, steps=3)
    assert upper_check.lo > 1
    # A narrow bracket for the unique scalar root is certified independently.
    beta_lo = F("3.92303796788587225299")
    beta_hi = F("3.92303796788587225301")
    left = normalized_p(beta_lo, steps=3)
    right = normalized_p(beta_hi, steps=3)
    assert left.hi < 1 < right.lo

    # Method-local obstruction. These numbers are NOT an actual spectral point.
    c = F(39, 40)
    x = F(39, 10)**3
    q0 = (Interval.exact(x) + pow_two_thirds(18)).div_positive(68)
    e0 = (pow_two_thirds(1782) - pow_two_thirds(18).square()).div_positive(68**2)
    assert q0.hi < c
    assert e0.hi < c - c*c
    assert 72**2 < 18**3                 # 72**(2/3) < 18
    tail_bound = F(9, 34)**4
    assert tail_bound < c - c*c

    # t_j > 8**(2**j) underlies the all-parameter monotonicity proof.
    assert rows[0][1] > 8
    for j, (d, t, M) in enumerate(rows):
        assert t > 8**(2**j)
        assert t <= M
        if j:
            assert t > rows[j-1][1]**2

    return {
        "status": "EXACT_CERTIFICATES_PASS; AC-04_NOT_SOLVED",
        "arithmetic": "Python integers and fractions.Fraction; decimal fields are display only",
        "claimed_upper_bound": str(alpha),
        "certified_at": {"base_power_n": 3, "reextractions_j": 3, "theta": "2/3"},
        "normalized_polynomial_at_upper_bound": upper_check.as_json(),
        "positive_margin_lower_bound": str(upper_check.lo - 1),
        "scalar_root_bracket": {"lo": str(beta_lo), "hi": str(beta_hi),
                                "lo_decimal": decimal(beta_lo),
                                "hi_decimal": decimal(beta_hi),
                                "left_test": left.as_json(), "right_test": right.as_json()},
        "dimensions": [{"j": j, "d": d, "t": t, "M": M} for j, (d,t,M) in enumerate(rows)],
        "method_local_obstruction": {
            "scope": "Only the displayed n=3 binary-reextraction scalar inequalities; not a tensor lower bound",
            "formal_value_of_T": "39/10", "theta_each": "2/3", "induction_ceiling": str(c),
            "q0": q0.as_json(), "E0": e0.as_json(),
            "tail_upper_bound": str(tail_bound), "allowed_increment": str(c - c*c)
        }
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write detailed JSON certificate")
    args = parser.parse_args()
    result = certify()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"])
    print("Exact upper-bound test: q_3(3.923038,2/3) in")
    interval = result["normalized_polynomial_at_upper_bound"]
    print("  [", interval["lower_decimal_for_display"], ",", interval["upper_decimal_for_display"], "]")
    print("The interval lies strictly above 1.")
    print("Root bracket:", result["scalar_root_bracket"]["lo"], result["scalar_root_bracket"]["hi"])
    print("Method-local obstruction at 3.9: all base and induction checks pass.")
    print("The checker does not constitute a formal verification of Strassen duality or of the full written proof.")


if __name__ == "__main__":
    main()

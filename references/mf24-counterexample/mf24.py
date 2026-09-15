"""Weighted shifts and polynomial norms for the MF-24 counterexample.

Rows and columns start at zero. The theorem uses m >= 2 and t > 1;
t = 1 is also accepted as a coincident-matrix control.
"""

from collections.abc import Iterator
from itertools import accumulate
from math import isfinite, sqrt

import numpy as np


def _check_m(m: int) -> None:
    if isinstance(m, bool) or not isinstance(m, int) or m < 2:
        raise ValueError("m must be an integer at least 2")


def _check_t(t: float) -> None:
    if not isfinite(t) or t < 1:
        raise ValueError("t must be finite and at least 1")


def exponents(m: int, side: str) -> list[int]:
    """Return the exponents in the superdiagonal weights t**e_i."""
    _check_m(m)
    if side not in ("X", "Y"):
        raise ValueError("side must be 'X' or 'Y'")

    motif = [1] + [0] * (m - 1)
    bridges = [0] + [-1] * (m - 1)
    if side == "Y":
        bridges.reverse()

    word = motif.copy()
    for bridge in bridges:
        word.extend([bridge] + motif)
    return word


def heights(m: int, side: str) -> list[int]:
    """Return h(0), ..., h(N-1), the cumulative weight exponents."""
    return [0, *accumulate(exponents(m, side))]


def weighted_shift(m: int, t: float, side: str) -> np.ndarray:
    """Construct the actual dense matrix; use only for small examples."""
    _check_t(t)
    return np.diag([t**e for e in exponents(m, side)], k=1)


def scaled_polynomial_blocks(m: int, t: float, side: str) -> Iterator[np.ndarray]:
    """Yield the residue blocks of p_m(W) / t**2, one block at a time.

    The largest block has order m+1, whereas W has order (m+1)**2.
    Computing the scaled entries directly avoids first forming t**2.
    """
    _check_t(t)
    h = heights(m, side)
    for residue in range(m + 2):
        a = h[residue::m + 2]
        block = np.zeros((len(a), len(a)))
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                block[i, j] = t ** (a[j] - a[i] - 2)
        yield block


def scaled_polynomial_norm(m: int, t: float, side: str) -> float:
    """Compute ||p_m(W)||_2 / t**2 from the residue blocks."""
    return max(float(np.linalg.norm(block, 2))
               for block in scaled_polynomial_blocks(m, t, side))


def norm_ratio(m: int, t: float) -> float:
    """Compute ||p_m(X)||_2 / ||p_m(Y)||_2; the scaling cancels."""
    return (scaled_polynomial_norm(m, t, "X")
            / scaled_polynomial_norm(m, t, "Y"))


def ratio_lower_bound(m: int, t: float) -> float:
    """Evaluate the theorem's lower bound in floating-point arithmetic."""
    _check_m(m)
    _check_t(t)
    inverse_t = 1.0 / t
    return sqrt(m) / (1 + (m - 1) * inverse_t * inverse_t)

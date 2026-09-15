"""Floating-point checks and a small norm-ratio table.

Run: OPENBLAS_NUM_THREADS=1 python check_numeric.py
The SVD comparisons test finitely many shifts, not the all-shifts theorem.
"""

import numpy as np

from mf24 import (norm_ratio, scaled_polynomial_blocks, ratio_lower_bound,
                  scaled_polynomial_norm, weighted_shift)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def direct_polynomial(matrix: np.ndarray, m: int) -> np.ndarray:
    """Evaluate the polynomial through ordinary matrix multiplication."""
    step = np.linalg.matrix_power(matrix, m + 2)
    power = np.eye(matrix.shape[0])
    result = np.zeros_like(matrix)
    for _ in range(m):
        power = power @ step
        result += power
    return result


def check_shifted_singular_values() -> None:
    rng = np.random.default_rng(240914)
    shifts = [0, 1, -1, 1j, 1 + 1j, 1e-6 * (1 + 2j), 1e6 * (2 - 1j)]
    shifts += list(rng.normal(size=20) + 1j * rng.normal(size=20))
    count = 0
    worst = 0.0
    for m in range(2, 10):
        for t in (1.0, 1.01, 1.5, 4.0, 20.0):
            x = weighted_shift(m, t, "X")
            y = weighted_shift(m, t, "Y")
            identity = np.eye(x.shape[0])
            for z in shifts:
                scale = max(1.0, t, abs(z))
                sx = np.linalg.svd((x - z * identity) / scale, compute_uv=False)
                sy = np.linalg.svd((y - z * identity) / scale, compute_uv=False)
                error = float(np.max(np.abs(sx - sy)))
                require(error < 5e-13,
                        f"shifted SVD mismatch: m={m}, t={t}, z={z}, error={error}")
                worst = max(worst, error)
                count += 1
    print(f"PASS: {count} shifted SVD comparisons")
    print(f"      maximum absolute error after common scaling: {worst:.3e}")


def check_scaled_polynomial_blocks() -> None:
    count = 0
    for m in (2, 3, 4, 7):
        for t in (1.0, 1.5, 4.0):
            for side in ("X", "Y"):
                w = weighted_shift(m, t, side)
                direct = direct_polynomial(w, m) / t**2
                order = [i for residue in range(m + 2)
                         for i in range(residue, w.shape[0], m + 2)]
                permuted = direct[np.ix_(order, order)]
                assembled = np.zeros_like(direct)
                offset = 0
                for block in scaled_polynomial_blocks(m, t, side):
                    size = len(block)
                    assembled[offset:offset + size, offset:offset + size] = block
                    offset += size
                require(np.allclose(permuted, assembled, rtol=3e-13, atol=3e-14),
                        "direct polynomial differs from residue blocks")
                full_norm = np.linalg.norm(direct, 2)
                block_norm = scaled_polynomial_norm(m, t, side)
                require(np.isclose(full_norm, block_norm, rtol=3e-13, atol=3e-14),
                        "dense and block operator norms differ")
                count += 1
    print(f"PASS: {count} dense polynomial and block-norm comparisons")


def check_bounds() -> None:
    count = 0
    for m in range(2, 21):
        for t in (1.0, 1.000001, 1.5, 4.0, 20.0, 1e6, 1e200):
            numerator = scaled_polynomial_norm(m, t, "X")
            denominator = scaled_polynomial_norm(m, t, "Y")
            require(numerator >= np.sqrt(m) * (1 - 3e-13), "numerator bound failed")
            upper = 1 + (m - 1) * (1 / t) * (1 / t)
            require(denominator <= upper * (1 + 3e-13), "denominator bound failed")
            require(denominator > 0, "zero polynomial denominator")
            require(numerator / denominator >= ratio_lower_bound(m, t) * (1 - 5e-13),
                    "ratio bound failed")
            if t == 1:
                require(np.isclose(numerator, denominator, rtol=3e-13),
                        "coincident-matrix control failed")
            count += 1
    print(f"PASS: {count} norm-bound comparisons, including t=1 and t=1e200")


def check_negative_control() -> None:
    m, t = 4, 4.0
    x = weighted_shift(m, t, "X")
    wrong = weighted_shift(m, t, "Y")
    i, j = (m - 1) * (m + 1) - 1, m * (m + 1) - 1
    wrong[i, i + 1], wrong[j, j + 1] = wrong[j, j + 1], wrong[i, i + 1]
    identity = np.eye(x.shape[0])
    sx = np.linalg.svd(x - identity, compute_uv=False)
    sy = np.linalg.svd(wrong - identity, compute_uv=False)
    require(np.max(np.abs(sx - sy)) > 1e-6,
            "SVD test missed the misplaced bridge")
    print("PASS: shifted SVD test rejects the misplaced-bridge control")


def print_table() -> None:
    print("\n  m       N       computed ratio      lower-bound formula")
    for m in (2, 3, 4, 9, 19, 49, 99):
        ratio = norm_ratio(m, float(m))
        lower = ratio_lower_bound(m, float(m))
        print(f"{m:3d} {(m + 1)**2:7d} {ratio:20.8f} {lower:24.8f}")
    print("\nBoth columns are rounded floating-point values.")
    print("Large-order polynomial norms use residue blocks, not dense shifted SVDs.")


def main() -> None:
    check_shifted_singular_values()
    check_scaled_polynomial_blocks()
    check_bounds()
    check_negative_control()
    print_table()
    print("All numerical checks passed. Small singular values have no relative-error guarantee.")


if __name__ == "__main__":
    main()

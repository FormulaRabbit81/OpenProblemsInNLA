#!/usr/bin/env python3
"""Recompute He's three prior examples and the later formalized example exactly.

Uses only rational arithmetic and the canonical IE-18 residual map. Run from
any directory; JSON is written to stdout and no archived source is modified.
"""
from fractions import Fraction as Q
from itertools import combinations
import json


def residual(matrix_diagonal, vector):
    av = [(1 - m) * x for m, x in zip(matrix_diagonal, vector)]
    denominator = sum(x * x for x in av)
    if denominator == 0:
        raise ValueError("The selected examples must have a nonzero denominator")
    alpha = sum(x * y for x, y in zip(vector, av)) / denominator
    return alpha, [m * (x - alpha * y)
                   for m, x, y in zip(matrix_diagonal, vector, av)]


def check(name, a, v, expected_bound):
    a, v = list(map(Q, a)), list(map(Q, v))
    m = [1 - x for x in a]
    if any(x == 0 for x in a) or all(x == 0 for x in m):
        raise ValueError("Inadmissible example")
    alpha, first = residual(m, v)
    beta, second = residual(m, first)
    pair_values = []
    for x, y in combinations(m, 2):
        denominator = abs(x * (x - 1)) + abs(y * (y - 1))
        pair_values.append((x * y * (y - x) / denominator) ** 2
                           if denominator else Q(0))
    bound = max(pair_values)
    squared_ratio = sum(x * x for x in second) / sum(x * x for x in v)
    if bound != Q(expected_bound) or squared_ratio <= bound ** 2:
        raise ValueError("The claimed exact counterexample did not verify")
    return {
        "example": name, "A_diagonal": list(map(str, a)),
        "M_diagonal": list(map(str, m)), "v": list(map(str, v)),
        "alpha": str(alpha), "first_residual": list(map(str, first)),
        "beta": str(beta), "second_residual": list(map(str, second)),
        "pairwise_norm_bound": str(bound),
        "squared_norm_ratio": str(squared_ratio),
        "squared_bound": str(bound ** 2),
        "strict_rational_gap": str(squared_ratio - bound ** 2),
        "result": "PASS",
    }


if __name__ == "__main__":
    examples = [
        ("He (2025), Example 2.1, A1", [1, 2, 3], [15, 5, 1], "1/16"),
        ("He (2025), Example 2.1, A2", ["-1/2", -4, 2], [38, 1, 45], "225/121"),
        ("He (2025), Example 2.1, A3", ["1/2", "3/2", "1/3", -2], [23, 60, 77, 1], "49/81"),
        ("Colbrook (2026), later Lean-formalized example", ["9/10", "1/2", "2/5"], [1, 1, 1], "1/121"),
    ]
    print(json.dumps([check(*example) for example in examples], indent=2))

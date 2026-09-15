"""Independent rational model check of IE-15 path/sign reductions; no proof claim."""
from fractions import Fraction as F
from pathlib import Path
import itertools
import json
import random


def swap(x, a, b):
    return b if x == a else a if x == b else x


def step(s, k, r, c):
    n = len(s)
    b = [[s[swap(i, k, r)][swap(j, k, c)] for j in range(n)] for i in range(n)]
    assert b[k][k]
    return [[b[i][j] - b[i][k] * b[k][j] / b[k][k]
             if i > k and j > k else F(0) for j in range(n)] for i in range(n)]


def rook(s, k, r, c):
    n = len(s)
    p = abs(s[r][c])
    return bool(p) and all(abs(s[r][j]) <= p for j in range(k, n)) and all(
        abs(s[i][c]) <= p for i in range(k, n))


def all_paths(a):
    n = len(a)
    def go(s, k, path, stages):
        if k == n:
            yield path, stages
            return
        for r, c in itertools.product(range(k, n), repeat=2):
            if rook(s, k, r, c):
                yield from go(step(s, k, r, c), k + 1, path + [(r, c)], stages + [s])
    yield from go(a, 0, [], [])


def tail(p, k, i):
    if k == len(p):
        return i
    return swap(tail(p, k + 1, i), k, p[k])


def no_swap_stages(a):
    s = a
    result = []
    for k in range(len(a)):
        assert rook(s, k, k, k)
        result.append(s)
        s = step(s, k, k, k)
    return result


def sign(x):
    return F(1 if x >= 0 else -1)


def check(a, path, original):
    n = len(a)
    pr, pc = zip(*path)
    b = [[a[tail(pr, 0, i)][tail(pc, 0, j)] for j in range(n)] for i in range(n)]
    bs = no_swap_stages(b)
    for k in range(n):
        for i, j in itertools.product(range(n), repeat=2):
            assert bs[k][i][j] == original[k][tail(pr, k, i)][tail(pc, k, j)]
        assert max(abs(bs[k][i][j]) for i in range(k, n) for j in range(k, n)) == max(
            abs(original[k][i][j]) for i in range(k, n) for j in range(k, n))
    maximum = max(abs(x) for row in b for x in row)
    assert maximum > 0
    last = n - 1
    pivots = [bs[k][k][k] for k in range(n)]
    lower = [bs[k][last][k] / pivots[k] for k in range(n)]
    rows = [F(1) if k == last else sign(lower[k]) for k in range(n)]
    cols = [rows[k] * sign(pivots[k]) for k in range(n)]
    d = [[rows[i] * b[i][j] * cols[j] / maximum for j in range(n)] for i in range(n)]
    ds = no_swap_stages(d)
    assert max(abs(x) for row in d for x in row) == 1
    for k in range(n):
        assert ds[k][k][k] > 0
        if k < last:
            assert ds[k][last][k] / ds[k][k][k] >= 0
        for i, j in itertools.product(range(n), repeat=2):
            assert abs(ds[k][i][j]) == abs(bs[k][i][j]) / maximum


rng = random.Random(20260915)
matrices = []
for n in range(1, 5):
    matrices.append([[F(int(i == j) * (-1 if i % 2 else 1)) for j in range(n)] for i in range(n)])
    for _ in range(15):
        matrices.append([[F(rng.randrange(-2, 3)) for j in range(n)] for i in range(n)])
counts = {str(n): 0 for n in range(1, 5)}
empty = 0
for a in matrices:
    local = 0
    for path, stages in all_paths(a):
        check(a, path, stages)
        counts[str(len(a))] += 1
        local += 1
    empty += local == 0
result = {
    "scope": "finite independent rational semantic checks; no universal proof or kernel result",
    "seed": 20260915,
    "input_matrices": len(matrices),
    "matrices_without_complete_nonzero_rook_path": empty,
    "checked_complete_paths_by_order": counts,
    "checked_complete_paths_total": sum(counts.values()),
    "permutation_trajectory_identity": "all checked stages and entries agree",
    "active_maximum_preservation": "all checked stages agree",
    "sign_scale_trajectory_identity": "all checked stages and entries agree",
    "normalization": "all checked pivots positive, initial max one, final-row lower multipliers nonnegative",
}
Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))

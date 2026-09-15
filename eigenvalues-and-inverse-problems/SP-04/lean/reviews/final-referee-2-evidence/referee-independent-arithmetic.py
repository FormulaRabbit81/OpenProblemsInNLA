#!/usr/bin/env python3
"""Referee-2 reconstruction using exact rationals and permutation determinants.

This is diagnostic evidence, not a proof of the real-quantified Lean target.
It does not import or execute the submitted diagnostic implementation.
"""
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path
import json


def determinant(a):
    total = Q(0)
    for p in permutations(range(len(a))):
        term = Q(-1 if sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))) % 2 else 1)
        for i, j in enumerate(p):
            term *= a[i][j]
            if not term:
                break
        total += term
    return total


def companion_tensor(s, c):
    indices = list(product(range(2), repeat=3))
    factors = [[[a, -c], [Q(1), Q(0)]] for a in s]
    def entry(i, j):
        value = Q(1)
        for k in range(3):
            value *= factors[k][i[k]][j[k]]
        return value
    return [[entry(i, j) for j in indices] for i in indices]


def eliminant(s, c):
    k = companion_tensor(s, c)
    return determinant([[k[i][j] - int(i == j) for j in range(8)] for i in range(8)]) * determinant([[k[i][j] + int(i == j) for j in range(8)] for i in range(8)])


center = [Q(a, 1000) for a in (1751, 1755, 1759)]
ends = [Q(a, 1000) for a in (1750, 1752, 1754, 1756, 1758, 1760)]
values = [determinant([[z*z - center[i]*center[i] if i == j else Q(0) for j in range(3)] for i in range(3)]) for z in ends]
assert [int(v > 0) - int(v < 0) for v in values] == [-1, 1, 1, -1, -1, 1]
pair_products = [values[2*i] * values[2*i+1] for i in range(3)]
assert all(v < 0 for v in pair_products)
assert all(0 < ends[i] < ends[i+1] for i in range(5))
assert ends[0] == Q(7, 4) and ends[-1] == Q(44, 25)

margins = [Q(49,16)-Q(52,25)-Q(99,100)**2,
           2-Q(275,198),
           1-Q(13,25)*Q(44,25)*Q(51,50),
           Q(13,25)-Q(201,400)]
assert all(v > 0 for v in margins)
assert margins == [Q(3,1250), Q(11,18), Q(1039,15625), Q(7,400)]
assert 2*Q(44,25)/(2*Q(99,100)) == Q(16,9)
assert (1+Q(16,9))/2 == Q(275,198)
assert Q(275,198)*(Q(44,25)-Q(7,4)) == Q(1,72) < Q(1,50)
assert 4-2*Q(7,4)-Q(13,25) == -Q(1,50)

t = Q(199, 400)
x = [-Q(1000000, 4020021), Q(2003, 1000), Q(2007, 1000)]
s = [a-t/a for a in x]
y = [abs(a) for a in x]
assert Q(7,4) < s[0] < s[1] < s[2] < Q(44,25)
assert 0 < t < Q(13,25)
assert x[0]*x[1]*x[2] == -1 and y[0]*y[1]*y[2] == 1
assert all(a*a - b*a - t == 0 for a,b in zip(x,s))
improvement = sum((a-b)**2-(a-d)**2 for a,b,d in zip(s,x,y))
assert improvement == 4*s[0]*abs(x[0]) > 0
k = companion_tensor(s, -t)
v = [x[0]**(1-i)*x[1]**(1-j)*x[2]**(1-l) for i,j,l in product(range(2), repeat=3)]
assert v[-1] == 1
assert [sum(a*b for a,b in zip(row,v)) for row in k] == [-a for a in v]
assert eliminant(s,-t) == 0
zero_checks = []
for data in (center,s):
    expected = 1-(data[0]*data[1]*data[2])**2
    assert eliminant(data,0) == expected < 0
    zero_checks.append(expected)

report = {
    'scope': 'Independent exact arithmetic diagnostics, not real-quantified proof or formal verification.',
    'method': 'Fractions, explicit tensor entries, and full permutation determinant formula; no submitted code imported.',
    'center': list(map(str,center)),
    'squared_endpoints': [str(a*a) for a in ends],
    'gram_values': list(map(str, values)),
    'three_negative_products': list(map(str,pair_products)),
    'four_challenge_inequality_margins': list(map(str,margins)),
    'auxiliary_stationary_data': list(map(str,s)),
    'auxiliary_stationary_entries': list(map(str,x)),
    'auxiliary_multiplier': str(-t),
    'auxiliary_squared_improvement': str(improvement),
    'tensor_eigenvector': list(map(str,v)),
    'eliminant_at_auxiliary_multiplier': '0',
    'eliminant_at_zero_center_then_auxiliary': list(map(str,zero_checks)),
    'all_assertions_passed': True,
}
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: six exact Gram signs, three negative endpoint products, four Challenge inequalities, rational-root bounds, exact auxiliary witness and tensor eliminant checks.')

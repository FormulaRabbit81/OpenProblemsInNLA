#!/usr/bin/env python3
"""High-precision exploratory values. NOT used for the exact certificate."""
from __future__ import annotations
import argparse
import sys
import mpmath as mp


def endpoint_bound(n: int, j: int):
    if n < 3 or j < 0:
        raise ValueError("Require initial power n >= 3 and iterations j >= 0")
    theta = mp.mpf(2)/3
    M = 4**n + 2**n
    delta = M - 3*3**n
    ts = [(M**(2**i)+2*delta**(2**i))//3 for i in range(j+1)]
    u = (mp.mpf(4**n)+mp.mpf(2**n)**theta)**(2**j)
    for i in range(j,0,-1):
        arg = u - mp.mpf(ts[i])**theta + mp.mpf(ts[i-1])**(2*theta)
        if arg <= 0:
            raise ArithmeticError("Invalid radicand: increase precision or inspect parameters")
        u = mp.sqrt(arg)
    x = u - mp.mpf(ts[0])**theta
    if x <= 0:
        raise ArithmeticError("Nonpositive endpoint x")
    return x**(mp.mpf(1)/n)


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--digits',type=int,default=100)
    p.add_argument('--steps',type=int,default=5)
    args=p.parse_args()
    if args.digits < 40 or not 0 <= args.steps <= 8:
        p.error('Require digits >= 40 and 0 <= steps <= 8')
    mp.mp.dps=args.digits
    print('EXPLORATORY VALUES ONLY; exact proof uses certify.py', file=sys.stderr)
    print('n,j,endpoint_bound')
    for n in (3,4):
        for j in range(args.steps+1):
            print(f'{n},{j},{mp.nstr(endpoint_bound(n,j),35)}')


if __name__ == '__main__':
    main()

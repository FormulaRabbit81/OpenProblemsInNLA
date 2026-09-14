"""Shared indexing and exact linear-algebra helpers (no symbolic simplifier)."""
from __future__ import annotations
from pathlib import Path
from itertools import product
import json
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
PRIME = 1_000_003

def load_scheme(name: str) -> np.ndarray:
    obj = json.loads((ROOT / 'data' / f'{name}.json').read_text())
    f = np.array([obj[x] for x in ('U', 'V', 'W')], dtype=np.int64)
    if f.shape != (3, 23, 9) or not np.all(np.isin(f, [-1, 0, 1])):
        raise ValueError('Expected three 23 x 9 signed-integer factor arrays.')
    return f

def target(a: int, b: int, c: int) -> int:
    return int(a // 3 == c // 3 and a % 3 == b // 3 and b % 3 == c % 3)

def tensor() -> np.ndarray:
    t = np.zeros((9, 9, 9), dtype=np.int64)
    for i, j, k in product(range(3), repeat=3):
        t[3*i+j, 3*j+k, 3*i+k] = 1
    return t

def support_system(f: np.ndarray):
    """Polynomials in normalized permitted entries; include the constant -1."""
    labels = [(g,t,k) for g,t,k in product(range(3),range(23),range(9)) if f[g,t,k]]
    vmap = {label: i for i, label in enumerate(labels)}
    polynomials = []
    for a,b,c in product(range(9), repeat=3):
        terms = []
        for t in range(23):
            keys = [(g,t,k) for g,k in enumerate((a,b,c))]
            if all(key in vmap for key in keys):
                terms.append((int(f[0,t,a]*f[1,t,b]*f[2,t,c]),
                              tuple(vmap[key] for key in keys)))
        if target(a,b,c):
            terms.append((-1, ()))
        polynomials.append(terms)
    return labels, polynomials

def exponent(monomial, n: int) -> list[int]:
    e = [0] * n
    for j in monomial:
        e[j] += 1
    return e

def jacobian(f: np.ndarray) -> np.ndarray:
    j = np.zeros((729,621), dtype=np.int64)
    for g,t,k in product(range(3),range(23),range(9)):
        fs = f[:,t,:].copy()
        fs[g] = 0
        fs[g,k] = 1
        j[:,g*207+t*9+k] = np.einsum('a,b,c->abc', *fs).reshape(-1)
    return j

def rank_mod(a: np.ndarray, p: int = PRIME):
    """Exact Gaussian elimination mod p, with original pivot row/column labels.

    Inputs here are small integers. At p=1000003, all intermediate products
    are below 10^12, so the vectorized int64 operations cannot overflow.
    """
    if p > 2_000_000 or p < 2:
        raise ValueError('This implementation restricts p for int64 safety.')
    a = np.asarray(a, dtype=np.int64).copy() % p
    m,n = a.shape
    rows = list(range(m)); cols = []; r = 0
    for c in range(n):
        nz = np.flatnonzero(a[r:,c])
        if len(nz) == 0:
            continue
        k = r + int(nz[0])
        a[[r,k]] = a[[k,r]]
        rows[r], rows[k] = rows[k], rows[r]
        a[r,c:] = a[r,c:] * pow(int(a[r,c]), -1, p) % p
        if r+1 < m:
            a[r+1:,c:] = (a[r+1:,c:] - a[r+1:,c,None]*a[None,r,c:]) % p
        cols.append(c); r += 1
        if r == m:
            break
    return r, rows[:r], cols

def tangent_directions(f: np.ndarray, labels, e: np.ndarray) -> np.ndarray:
    """58 monomial-parameter derivatives + 18 off-diagonal basis derivatives."""
    h = np.zeros((621, e.shape[1]+18), dtype=np.int64)
    for row,(g,t,k) in enumerate(labels):
        h[g*207+t*9+k,:e.shape[1]] = f[g,t,k] * e[row]
    mats = f.reshape(3,23,3,3)
    col = e.shape[1]
    for g in range(3):
        for a,b in product(range(3), repeat=2):
            if a == b:
                continue
            d = np.zeros((3,3), dtype=np.int64); d[a,b] = 1
            df = np.zeros_like(mats)
            if g == 0:
                df[0] = d.T @ mats[0]; df[2] = -d @ mats[2]
            elif g == 1:
                df[0] = -mats[0] @ d.T; df[1] = d.T @ mats[1]
            else:
                df[1] = -mats[1] @ d.T; df[2] = mats[2] @ d
            h[:,col] = df.reshape(-1); col += 1
    return h

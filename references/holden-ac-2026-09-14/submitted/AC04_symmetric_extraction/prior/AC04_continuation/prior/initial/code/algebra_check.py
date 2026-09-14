#!/usr/bin/env python3
"""Exact finite-dimensional algebra audit (requires SymPy).

Verifies the normal form, four-term decomposition, contraction factorization,
and the full 72-dimensional base slice extraction. No approximate rank tests.
"""
from __future__ import annotations
import argparse
from itertools import product, permutations
import json
from pathlib import Path
import sympy as sp


def check() -> dict:
    vectors = [(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)]
    V = sp.Matrix.hstack(*(sp.Matrix(v) for v in vectors))
    for i,j,k in product(range(3), repeat=3):
        coeff = sum(sp.Rational(v[i]*v[j]*v[k],4) for v in vectors)
        assert coeff == int(len({i,j,k}) == 3)

    # T = (1/2) L^{tensor 3} P, with L columns e_0,e_1+i e_2,e_1-i e_2.
    L = sp.Matrix([[1,0,0],[0,1,1],[0,sp.I,-sp.I]])
    assert L.det() != 0
    for i,j,k in product(range(3), repeat=3):
        coeff = sp.expand(sum(L[i,a]*L[j,b]*L[k,c]/2
                         for a,b,c in permutations(range(3))))
        target = int(sorted((i,j,k)) in ([0,1,1],[0,2,2]))
        assert coeff == target

    flat = sp.Matrix(3,9, lambda i,j: int(len({i,j//3,j%3}) == 3))
    assert flat.rank() == 3

    D = sp.diag(1,1,-1,-1)
    M = V*D*V.T
    X = sp.Matrix([[0,0],[4,0],[0,4]])
    Y = sp.Matrix([[0,0],[0,1],[1,0]])
    assert M == X*Y.T and M.rank() == 2

    A = sp.kronecker_product(V,V,V)
    DD = sp.kronecker_product(D,D,D)
    XX = sp.kronecker_product(X,X,X)
    YY = sp.kronecker_product(Y,Y,Y)
    Abar, Bbar = A.row_join(XX), A.row_join(YY)
    H = sp.diag(DD, -sp.eye(8))
    assert H.det() != 0 and H.shape == (72,72)
    assert Abar.rank() == Bbar.rank() == 27
    assert Abar*H*Bbar.T == sp.zeros(27)

    # Row maps for the two annihilator subspaces in the extraction lemma.
    N1 = sp.Matrix.hstack(*(Bbar*H.T).nullspace())
    N2 = sp.Matrix.hstack(*(Abar*H).nullspace())
    assert N1.shape == N2.shape == (72,45)
    assert N1.T*H*Bbar.T == sp.zeros(45,27)
    assert Abar*H*N2 == sp.zeros(27,45)
    Q = N1.T*H*N2
    assert Q.rank() == 18
    columns = Q.rref()[1]
    rows = Q[:,list(columns)].T.rref()[1]
    minor = Q.extract(rows, columns)
    determinant = minor.det()
    assert len(rows) == len(columns) == 18 and determinant != 0
    return {
        "status": "EXACT_ALGEBRA_CHECKS_PASS",
        "sympy_version": sp.__version__,
        "normal_form_coefficient_checks": 27,
        "rank_four_decomposition_coefficient_checks": 27,
        "flattening_rank": 3,
        "sign_contraction_matrix": [list(M.row(i)) for i in range(3)],
        "sign_contraction_rank": 2,
        "base_source_dimension": 72,
        "base_source_contraction_determinant": H.det(),
        "annihilator_dimensions": [45,45],
        "compressed_matrix_dimension": [45,45],
        "compressed_rank": 18,
        "nonzero_minor_rows_zero_indexed": list(rows),
        "nonzero_minor_columns_zero_indexed": list(columns),
        "nonzero_minor_determinant": determinant,
        "scope": "Finite algebra only; not a formal verification of the asymptotic proof"
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    results = check()
    text = json.dumps(results, indent=2, default=str) + "\n"
    print(text, end="")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()

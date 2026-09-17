# Primary reuse for polynomial Schur clauses

The accepted plan steps11-15 are implemented in SchurPolynomial.lean.
Pinned polynomial Degree/Operations supplies degree_smul_le, degree_mul_X and
degree_add_eq_right_of_degree_lt; Degree/Defs supplies degree_mul_le_of_le.
Polynomial/Inductions:X_mul_divX_add supplies the explicit Bezout witnesses
for X and b, and RingTheory/Coprime/Basic:IsCoprime.mul_left combines them.
Data/Complex/Basic:normSq_add, normSq_mul, normSq_conj, mul_conj and
Analysis/Complex/Norm:sq_norm reduce the scalar defect to ring algebra.

This is a helper candidate, not frozen contract14 completion. No extra
assumption is exported: degree, constant coefficient, old coprimality and
old disk/boundary properties are explicit inputs to their exact transformations.
The parameter c=0 is permitted, and nonvanishing is on the closed disk.
No compiler, cache, Git, network or numerical interval computation ran.

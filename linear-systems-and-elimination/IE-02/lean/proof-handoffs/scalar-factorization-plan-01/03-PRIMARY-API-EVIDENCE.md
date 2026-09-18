# Primary reuse and precise pending boundary

Polynomial.eval_mul (Eval/Defs612) and existing reflection_evaluation19 give
the circle product identity. Complex.mul_conj (Data/Complex/Basic587) and
Complex.sq_norm (Analysis/Complex/Norm150) identify the actual complex product
with the embedded real square norm. No integral or coefficient proof is redone.

sumSquares_pos is an existing project theorem in FourierSupport, imported by
EffectivePolynomial. It supplies Q(1)>0 from the actual nonzero evaluation.
Algebra/Order/GroupWithZero/Basic531 supplies sq_pos_of_pos and880 div_pos;
GroupWithZero/Units/Basic348 supplies eq_div_iff after the explicit nonzero
denominator proof. Complex.ofReal_div733, ofReal_mul223 and ofReal_injective103
identify the exact complex kappa with a positive real beta.

weighted_fold21 is genuinely reused twice: on Fin1 for strict real-sqrt
rescaling, and on the original family for arbitrary nonnegative weights.
Algebra/BigOperators/Fin107 supplies Fin.sum_univ_one; the already-proved
weighted_fold contains Real.sqrt_nonneg/Real.sq_sqrt and norm compatibility.

Nat.strong_induction_on (Data/Nat/Init260) supports the weak degree induction.
CommonCircleRoot22 supplies degree lowering including zero quotients.
Polynomial.degree_X_sub_C (Degree/Operations756) and degree_mul_le_of_le
(Degree/Defs398) give the reconstruction degree. Explicit WithBot casts and
Nat.cast_add avoid the previously observed degree elaboration mismatch.

Polynomial.eval_finsetSum (Eval/Defs349, use this current name) and
Complex.ofReal_sum (Data/Complex/BigOperators29) handle the weighted sum.
Existing circle_polynomial_uniqueness20 closes the exact polynomial identity
without requiring a coefficient bound or a finite-grid uniqueness assumption.

Current effective24 source is matched to successful actual102, and common-root22
to actual66 (with the documented redundant hz warning). Raw logs were read and
receipt/source hashes checked. Other existing helper sources are bound, without
new runtime claims. Exact25/26 are pending independent implementation: the
other author reports intended ReciprocalRoots.lean / InsideFactor.lean with
ell=0, repeated roots and a merely complex nonzero kappa included. That report
is not a proof acceptance; no corresponding placeholder dependency is allowed.

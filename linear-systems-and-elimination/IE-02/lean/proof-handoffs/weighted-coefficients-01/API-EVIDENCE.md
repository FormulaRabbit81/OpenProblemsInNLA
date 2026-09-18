# Weighted coefficient preservation: primary reuse evidence

Mathlib is read-only at pin 0df444a360eaa60ab8c11dca51a86af692955474. Project
source bindings and the main library file hashes precede coding in
01-PRE-CODE-BINDINGS.json and are rechecked at seal. This note describes source
inspection, not a compiler result or independent proof review.

| API | Exact role |
| --- | --- |
| Coefficients.lean, coefficient_inner_product, second conjunct | Coefficient N of reflected f*g times r*(b*g) equals the actual complex Euclidean coefficient inner product, with no bound on the second polynomial. |
| Reflection.lean, reflection_product | The fixed reflection bound is d+m even when a factor has smaller degree or is zero. No coefficient reimplementation is introduced. |
| Toeplitz.lean, toeplitz_action | Rewrites the actual Euclidean matrix action as coefficient multiplication against vectorPolynomial. |
| Toeplitz.lean, coeffVector_mul_truncate | Removes vectorPolynomial(coeffVector p) only under the enclosing finite coefficient product, valid for arbitrary polynomial degrees. |
| Algebra/Polynomial/Degree/Defs.lean:398, degree_mul_le_of_le | Produces the exact degree bound for f*g, including zero factors. WithBot.coe_add supplies the fixed natural-bound arithmetic. |
| Algebra/Polynomial/Coeff.lean:90, finsetSum_coeff | Linear extraction of coefficient N from the finite polynomial sum. |
| Algebra/Polynomial/Coeff.lean:156, coeff_C_mul | The complex embedded real weight factors out of the coefficient. |
| Data/Complex/BigOperators.lean:44, Complex.re_sum | Real parts commute with the finite sum, including the empty sum. |
| Data/Complex/Basic.lean:226, Complex.re_ofReal_mul | Uses the explicit complex real cast; no positivity restriction. This specializes the generic API named in the plan. |
| Analysis/InnerProductSpace/Basic.lean:53, exported norm_sq_eq_re_inner | After fixing 𝕜=ℂ, self-inner-product real parts are squared Euclidean norms. |

The private helper is a reusable complex pairing identity. It factors each
reflected product as S*(g*conjReflect m g), substitutes the provided factor
identity, and uses coefficient linearity. Polynomial reassociation uses
`ac_rfl` on a fixed number of symbolic factors; no computation grows with the
dimensions or polynomial degrees. The norm and direction branches instantiate
that one helper. The norm branch alone applies Complex.re; the direction
branch retains the full complex equality.

No separate factorization theorem is assumed by the helper: hfactor is
exactly the hypothesis in the frozen contract being implemented. No norm
identity, Toeplitz action, degree estimate, or high-degree truncation is added
as a new axiom. All are derived or reused from the bound sources above.

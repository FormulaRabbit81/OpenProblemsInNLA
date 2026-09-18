# Pinned primary reuse evidence

All paths below are read-only primary Mathlib sources at
`0df444a360eaa60ab8c11dca51a86af692955474`. Exact full-file SHA-256 bindings and
source-matched prior local receipts are in 02-SOURCE-BINDINGS.json. This evidence
is an implementation plan, not an elaboration claim.

| Source | Exact API / inspected location | Intended use |
|---|---|---|
| Mathlib/Analysis/InnerProductSpace/PiL2.lean | Matrix.toEuclideanLin, lines1243–1245 | Actual linear equivalence from complex matrices to Euclidean linear maps; inherit add, sub, sum and scalar laws. |
| Same | OrthonormalBasis.norm_eq_one, lines457–458; EuclideanSpace.basisFun, lines803–808 | Explicit unit vector for n ≥ 1 even when the optimal residual is zero. |
| Mathlib/Analysis/InnerProductSpace/Basic.lean | inner_smul_right, lines115–116; inner_sum, lines162–164 | Full complex orthogonality extends to arbitrary complex direction sums in the correct, linear second slot. |
| Same | norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, lines564–569 | Complex Pythagoras; pinned RHS and LHS use products of norms despite the name. Explicit 𝕜 := ℂ avoids ambiguous real-inner-product inference. |
| Mathlib/Algebra/Order/GroupWithZero/Basic.lean | sq_le_sq₀, lines715–716 | Recover norm inequality from squared norm inequality using norm_nonneg for both operands. |
| Mathlib/Analysis/Normed/Operator/Basic.lean | ContinuousLinearMap.le_opNorm, line237 | Uniform bound using the actual frozen euclideanCLM operator norm; unit norm reduces the product to t. |
| Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean | IsGreatest.csSup_eq, lines70–73 | Actual outer supremum equals an explicitly constructed greatest element; proof internally supplies nonemptiness and boundedness. |
| Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean | map_prod and its generated additive map_sum, lines364–369 | Map finite sums through the proved Toeplitz algebra homomorphism and Euclidean linear equivalence. |
| Mathlib/Algebra/Algebra/Hom.lean | AlgHomClass to semilinear map class, lines56–65; AlgHom.toLinearMap, lines272–278 | Algebra homs preserve complex scalar multiplication; reuse toeplitzAlgHom instead of coefficient proofs. |

Existing project results are reused at their exact current source bytes:

* AffineMinima's actual operator and vector minima (42/43) already retain all
  dimensions and dependent/empty direction families. Current source passed
  local68, with both standard-three-axiom prints.
* NormAttainment, MaximalSpace and Toeplitz provide actual norms, the kernel
  characterization and the polynomial algebra homomorphism. The new affine
  proof does not assume a norm identity or redefine Toeplitz membership.
* JordanDirections (46), PolynomialResiduals (47), JordanReversal (45),
  JordanTransport (48) and GMRESSemantics (49) already passed local checks.
  The public polynomial_residual_value_set helper identifies actual sets;
  reverseVector_norm/involutive transport the entire sphere and each witness.
* MinimizerOrthogonality (41) is a root-owned candidate at planning time. Its
  frozen header is read and bound. This plan may depend on that exact contract,
  but implementation is gated on its actual successful local proof and root
  plan acceptance. No placeholder import is proposed.

The original finite paper route, section4 (attained affine minimax) and section5
(original Jordan interface), is also source-bound. Existing symbolic proofs
replace its generic nearest-point argument with already verified AffineMinima;
the numerical statements and canonical scope are unchanged.

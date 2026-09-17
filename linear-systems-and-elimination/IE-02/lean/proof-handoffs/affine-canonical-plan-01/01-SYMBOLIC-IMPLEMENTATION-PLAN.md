# Source-bound symbolic plan for exact contracts 44 and 50

This follows the separately written numerical/semantic targets. No Lean source
for these contracts is authored in this packet. The frozen names and headers,
not earlier message ordinal slips, are authoritative: minimizer_orthogonality is
41, affine_operator_minimum is 42, affine_vector_minimum is 43,
affine_minimax_attained is 44, and canonical_jordan_minimax is 50.

## AffineMinimax.lean: affine_minimax_attained (44)

1. Import the actual AffineMinima and MinimizerOrthogonality modules and the
   proved Toeplitz/MaximalSpace APIs as needed. Wait for root's actual successful
   41 prerequisite before implementing. Do not import Challenge. The linear
   matrix action is the frozen Matrix.toEuclideanLin map and the operator norm
   is the norm of its continuous extension.

2. Obtain c₀, its value equality, and its all-coefficients minimum inequality
   from affine_operator_minimum Y R. Define T = affineResidual Y R c₀ and
   t = operatorNorm T. Keep the tuple minimum, rather than assume independent
   directions or a unique coefficient representation.

3. Prove a small matrix algebra identity for direction sums: directionSum R is
   additive and complex linear in its tuple. Use Finset.sum_sub_distrib and
   sub_smul (or the corresponding sum identity after rewriting subtraction).
   In particular T + directionSum R c = affineResidual Y R (c₀ − c), and
   affineResidual Y R d = T + directionSum R (c₀ − d). These are identities
   in the additive group of matrices, with no multiplication-order issue.
   Applying the c₀ minimum to c₀ − c supplies every premise of 41's hmin.

4. Prove IsToeplitz T with actual polynomial witnesses. Choose p for Y and q_j
   for R_j from their supplied existential witnesses, and use
   p − Σ_j c₀(j) • q_j as a witness for T. Reuse toeplitzAlgHom and its map_sub,
   map_sum and map_smul laws; expose its underlying function only with a
   documented change where needed. Do not reprove coefficient convolution or
   rely on a matrix norm instance.

5. Produce one x₀ with norm one, ||T x₀|| = t, and
   ||T x₀|| ≤ ||affineResidual Y R d x₀|| for all d. Split only T = 0 versus
   T ≠ 0. For T = 0 choose the explicit vector
   (EuclideanSpace.basisFun (Fin n) ℂ) ⟨0, hn⟩. OrthonormalBasis.norm_eq_one
   proves it is unit. The zero matrix has zero Euclidean action and zero
   continuous-map norm, so both required value identities simplify to zero;
   norm_nonneg gives every comparison. This branch adds no nonzero hypothesis.

6. For T ≠ 0 apply actual minimizer_orthogonality hn T R to the witness from
   step 4 and the all-direction minimum from step 3. Its x₀ is in unitMaximal T
   and has inner ℂ (T x₀) (R_j x₀) = 0 for every j. From maximal_space_norm and
   ||x₀|| = 1 obtain ||T x₀|| = t. No choice of a single singular vector basis
   or assumption on the maximal singular multiplicity is needed.

7. For each d let v = Σ_j (c₀(j) − d(j)) • euclideanLin (R_j) x₀. The linear
   equivalence Matrix.toEuclideanLin, map_sum/map_smul/map_add and application
   lemmas give affineResidual Y R d acting on x₀ as T x₀ + v. inner_sum and
   inner_smul_right give the full complex inner product inner ℂ (T x₀) v = 0.
   Apply norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero with 𝕜 explicitly
   ℂ. Its pinned statement uses products of norms; rewrite with pow_two when
   convenient. Nonnegativity and sq_le_sq₀ give ||T x₀|| ≤ ||T x₀ + v||.
   This is a symbolic Pythagorean estimate, not a new interval certificate.

8. Reuse affine_vector_minimum at an arbitrary x. Its chosen tuple c_x proves
   0 ≤ affineInner Y R x and affineInner Y R x ≤ ||T x||. At x₀, combine its
   minimum with step 5's reverse comparison to prove
   affineInner Y R x₀ = ||T x₀|| = t. This handles the actual sInf definition
   through the already-proved attaining equality; no empty-set convention or
   unjustified infimum rewrite is used.

9. For every unit z, step 8 and (euclideanCLM T).le_opNorm z give
   affineInner Y R z ≤ t = affineInner Y R x₀. Thus the image defining
   affineWorst has the greatest element t, witnessed by x₀. Build IsGreatest
   explicitly and use IsGreatest.csSup_eq. Membership supplies nonemptiness and
   the comparison supplies boundedness. This produces the actual supremum
   equality and its attained maximum without a continuity assumption on the
   inner-minimum function.

10. Assemble the exact frozen conjunction. Preserve c₀'s operator minimum and
    its global inequality from 42; use 43 for each unit starting vector; use
    x₀'s norm attainment, vector minimum, and step 9 for every remaining
    witness/comparison clause. The proof includes n = 1 and k = 0, all dependent
    directions, and both zero/nonzero residual branches. Append the exact
    theorem's #print axioms and #assert_trust kernel.

## CanonicalJordan.lean: canonical_jordan_minimax (50)

11. Implement only after 44 itself has passed root's actual local compiler.
    Import AffineMinimax, JordanDirections, JordanTransport and GMRESSemantics;
    reuse PolynomialResiduals transitively or explicitly. Preserve the frozen
    n ≥ 2, lam ≠ 0, 1 ≤ k and k < n hypotheses. The transport route is stronger
    internally and may not need all of these restrictions; retain them literally
    and document any unused frozen hypotheses without artificial dependencies.

12. Put A = lowerJordan n lam, J = jordan n lam and R = jordanDirections n k lam.
    jordan_direction_toeplitz supplies IsToeplitz I and all IsToeplitz R_j.
    Apply 44 with the derived 1 ≤ n. Retain the full tuple c₀ and vector x₀
    certificate, not only its scalar equality.

13. Identify the lower GMRES value sets with the affine value sets before
    taking sInf. Reuse polynomial_residual_value_set A k operatorNorm for
    idealGMRES A k = affineIdeal I R, and the same theorem with
    f(B) = ||euclideanLin B x|| for gmresInner A k x = affineInner I R x.
    jordanDirections is definitionally the tuple of positive powers used by
    that helper. Alternatively the exact normalized_polynomial_residuals two
    directions can supply the same membership proof; no coefficient family is
    discarded.

14. For every admissible p, jordan_polynomial_transport yields equal operator
    norms of p(J) and p(A). Its vector clause and reverseVector_norm yield
    ||p(J) reverseVector x|| = ||p(A) x||. Prove equality of the corresponding
    polynomial value sets by retaining the same p and Admissible witness in
    both directions. Congruence of sInf then gives the upper/lower ideal
    equality and gmresInner J k (reverseVector x) = gmresInner A k x.

15. reverseVector_norm and reverseVector_involutive prove that reversal maps
    the entire unit sphere onto itself. For each upper unit z use lower vector
    reverseVector z; for each lower unit x use upper vector reverseVector x.
    Combine step 14's inner identity with step 13 to prove equality of the
    actual sets gmresInner J k '' unitSphere n and
    affineInner I R '' unitSphere n. Congruence of sSup gives
    worstGMRES J k = affineWorst I R. The scalar equality in 50 follows from
    44 and the ideal identities, without a separate minimax theorem.

16. For the pointwise inner-attainment clause use
    (gmres_extrema_semantics J k).2.1 x directly. This already supplies p,
    admissibility, equality to the actual gmresInner, and comparison against
    every admissible q. Restrict its all-x conclusion to the required unit
    vectors. Do not rederive the finite-dimensional nearest-point theorem.

17. Convert c₀ to one admissible p₀ using the second direction of
    normalized_polynomial_residuals. Set the upper witness y₀ = reverseVector x₀.
    Step 14 transports its norm and action and step 15 transports its inner
    maximum. For every admissible q, the first parameterization direction
    supplies a tuple d with q(A) = affineResidual I R d. Transfer the operator
    and vector comparisons from 44 using these two exact matrix identities.
    For every upper unit z, apply 44's outer comparison to reverseVector z and
    use involution to recover z. This certifies all final witness clauses.

18. Append the frozen theorem's #print axioms and #assert_trust kernel. Root
    alone compiles at the existing limits; source-only proof handoffs explicitly
    remain unrun until actual receipts arrive. This is the original canonical
    target, but its completion is claimed only after the whole exact source
    closure, independent review and final real GitHub Comparator checks required
    by the project workflow, not on the strength of this plan.

## Mathematical and elaboration assessment

No new mathematical obstacle is known. The remaining uncertainty is ordinary
Lean elaboration: underlying AlgHom versus toeplitz wrappers, linear-map versus
continuous-map application, and nested conjunction/image membership witnesses.
Use small explicitly typed identities at those boundaries, with comments that
explain the unchanged frozen meanings. Do not introduce new assumptions,
custom axioms, placeholders, resource overrides or extra numerical computation.

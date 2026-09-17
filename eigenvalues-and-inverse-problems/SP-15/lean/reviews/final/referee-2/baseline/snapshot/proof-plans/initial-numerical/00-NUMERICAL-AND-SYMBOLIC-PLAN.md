# SP-15 initial numerical batch — before implementation

Prepared by `/root/mi13_full_referee2` on 17 September 2026. Status: API-inspected proof plan only, awaiting the second independent statement review and root freeze acceptance. No Lean implementation or compiler invocation is authorized by this plan. The actual corrected draft local63 elaboration is a root result; it is not a proof result.

The exact mathematical boundary remains the current concrete Definitions (`fa57c71cd3e6d6551f081e479121f9f6a4695858732f3e6d1fa4cd79ad927498`) and corrected Challenge (`dc55eda7fac9d89e3c7017593ce3bdb6f8a4b01b15775d4c6f8c8e13b6560833`). `EXACT-HEADERS.json` retains the seven target headers verbatim. This batch covers contracts 1–4, 8, and 10–11 of 29. It does not establish the polynomial determinant identity, actual derivative, inverse-function bridge, positivity/square-root semantics, all-shift spectral transport, arbitrary-unitary rigidity, or the complete original dimension-nine counterexample.

## Numerical statements fixed before proof code

The box radius is exactly `r = 1/16`; the base point is `(1,2,3,4,4,4,1,1,1,1)`. The scalar certificate has five conjuncts: `r > 0`, `1-r > 0`, `1-2r > 0`, `3(1+r) < 4-r`, and `(4-r)-3(1+r) = 3/4`. The first four are closed rational strict inequalities; the last is a closed rational identity. No floating approximation, variable interval, or subdivision is needed.

The open parameter box must contain that actual base point. For every point in the box, each of its first three coordinates is positive, coordinates 6 and 7 are positive, and every actual `qMatrix` row satisfies

`sum of off-diagonal complex norms + 3/4 < real diagonal entry`.

For any two points in this same box, coordinates belonging to different `p` slots must differ. The centers 1, 2, 3 are one unit apart, while their total uncertainty is `2r < 1`.

The actual nine polynomial coordinates at the actual base point must equal

`(300,159,814,24,263,697,18,103,189)`.

For the actual first-nine-column `jacobianMinor`, prove the literal matrix equation `J9 = L*U`, the lower and upper triangular zero patterns, the unit lower diagonal, every nonzero upper pivot, and the product of upper pivots `-1088`. Then prove `det J9 = -1088` using determinant multiplicativity and triangular determinant theorems. The exact LU data and first-nine-column selection may not be replaced by a new matrix with an assumed derivative interpretation.

## Module and proof route

1. `Numerical.lean`: prove only `box_scalar_certificate`. Unfold the named radius into closed rational goals. Use `interval_decide (trust := kernel)` for the four strict inequalities with global `leancert.trust = "kernel"`; use exact `norm_num` for the final equality. Keep the public bundled theorem and assert its kernel trust. Do not invoke interval subdivision or widen the domain. The actual certificate must be consumed in the downstream box geometry, positivity bounds, and interval separation; no decorative unused LeanCert theorem is acceptable.

2. `BoxGeometry.lean`: prove `parameter_box_geometry`, `parameter_box_bounds`, and `p_intervals_separate`, importing the numerical module. Obtain a small private coordinate-bounds helper directly from `abs_lt.mp (hx i)`: `basePoint i-r < x i < basePoint i+r`. This helper has genuine consumers and does not assume an analytic theorem.

   For openness, rewrite the set of universally quantified coordinate inequalities using the current `Set.ofPred_forall` API, then use `isOpen_iInter_of_finite`. Each coordinate inequality is open by `isOpen_lt`, continuity of coordinate evaluation, subtraction of a constant, and continuity of the real norm. Convert the real norm to absolute value with `Real.norm_eq_abs`. This avoids a manual metric-ball argument and does not need an interval bound. At the base point every difference is zero; consume `box_scalar_certificate.1`.

   Positivity uses the lower coordinate bounds and the certificate's `1-r > 0`; the smallest relevant center is 1. On coordinates 6–9, the same bounds imply positivity and `|x i| < 1+r`. For Q's complex entries, reuse `Complex.norm_le_abs_re_add_abs_im` directly; the actual real/imaginary components of `c+I*d` and `c-I*d` give a bound by `|c|+|d|`. Use `Complex.norm_real` and `Real.norm_eq_abs` on the two real off-diagonal entries. Case analysis has only three rows. Row zero is bounded by `2(1+r)`, the other rows by `3(1+r)`. Use the already certified `1+r > 0` consequence and exact margin identity to reach the common strict `3/4` gap against the diagonal lower bound `4-r`. Do not approximate a square root, compute numerical eigenvalues, or duplicate the existing complex norm estimate.

   For the six unequal pairs of `p` slots, use the genuine coordinate bounds and `1-2r > 0`. Three equal-index cases contradict the supplied `i ≠ j`. Finite case analysis plus linear arithmetic suffices; the proof must retain two arbitrary points `x,y`, not prove only distinct coordinates at one point. Keep the radius symbolic after consuming the scalar certificate, so no redundant numerical certificate is rebuilt here.

3. `JacobianCertificate.lean`: prove `coefficient_base_value`, `jacobian_lu_certificate`, and `jacobian_minor_nonsingular`. Base-value equality is function extensionality followed by nine index cases and exact evaluation of the actual `coefficients` expression at the actual `basePoint`. Do not substitute preflight outputs as axioms, or conclude an actual derivative from this base-value check.

   For `J9=L*U`, use matrix extensionality, `Matrix.mul_apply`, and finite-sum expansion. Reduce the literal indices before normalizing rational arithmetic. Triangular zeros remove all but 285 scalar products across the 81 entries, compared with the unrestricted 729; the largest entry has nine terms. Use exact `norm_num`, with no `native_decide`, external oracle, custom axiom, or runtime evaluation of a real-valued predicate. One private reconstruction lemma is acceptable if it keeps the bundled public certificate readable. The already supplied LU certificate needs no row permutation.

   Triangularity is literal index comparison plus zero entries; diagonal units and nonzero pivots require nine cases each. Reuse `Fin.prod_univ_succ` (or the corresponding current vector-product simp APIs) for the nine-factor upper diagonal product. The exact pivot list is

   `300, 39/2, -100/39, 37123/1875, 345081/148492, -147294/115027, -1401/8183, 4186/37827, 136/2093`.

   Its successive products are the integers

   `300, 5850, -15000, -296984, -690162, 883764, -151308, -16744, -1088`.

   These small exact factors make extra interval machinery unnecessary. They are planning diagnostics only until the Lean proof is compiled.

   To prove the determinant, construct the actual `Matrix.IsLowerTriangular` and `Matrix.IsUpperTriangular` premises from the certificate, preserving their orientation. The lower predicate is block triangular for the dual order: `i<j` is the required vanishing condition. Apply current `Matrix.det_of_isLowerTriangular` (matrix argument explicit) and `Matrix.det_of_isUpperTriangular` (matrix implicit), plus `Matrix.det_mul`. Lower diagonal product is 1, upper diagonal product is -1088. Never unfold the 9×9 determinant definition or enumerate its 9! permutations. Do not use the deprecated `det_of_lowerTriangular`/`det_of_upperTriangular` aliases.

## Verification, scope, and later consumers

The exact literal coefficient/Jacobian/LU source diagnostic was already performed in statement preparation and independently checked by statement review1. This plan's small `Fraction` diagnostic checks only the planned LU workload and pivot products. It is neither the universal mathematical proof nor a formal certificate. No fresh statement verification is inferred from it.

Every new public theorem must preserve the frozen header exactly, be followed by actual axiom and kernel-trust checks in the implementation, and be tested by root's one serial local compiler before any push. Keep source and receipt hashes for every attempt. No local parallel compiler, GitHub debugging loop, local Comparator installation, or silent trust-mode fallback is permitted. Current source/API availability is documented separately from future elaboration success.

Most importantly, the LU result remains a fact about numerical matrix data until the later `coefficient_strict_derivative` proves that the actual polynomial coefficient map has the displayed actual derivative. Its downstream use must pass through that contract before the genuine inverse-function theorem. This first batch alone cannot count as a solved or Lean-verified problem.

Credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology; retain substantial OpenAI Codex assistance and the original Fortier Bourque/Ransford mathematical attribution. Publish no email. Central finite-matrix, topology, and complex-norm APIs are reused from the pinned Mathlib. The scalar kernel-mode pattern follows the already accepted MI-13 numerical module; the retained Forsythe and Schiffer examples supplied statement/proof separation patterns, not a proof of SP-15.

# SP-15 contracts 12–15: numerical obligations and proof route before code

Author: /root/mi13_full_referee2. Formalization attribution: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology. Substantial OpenAI Codex assistance; existing mathematical and code
authors retain their credit. No email is included. This is author planning, not
an independent referee review or an execution certificate.

This batch keeps all four exact frozen headers. The target is the actual augmented
coefficient map, its actual derivative, a genuine local inverse, and a nonempty
fiber inside the full original parameter box. No inverse function, nonsingular
derivative, constant fiber, or neighborhood radius is assumed.

## Exact numerical and structural statements to establish

Let J be the frozen 9×10 real Jacobian and K its first-nine-column minor. The
already proved LU certificate gives det K = −1088. Let A be the **actual** frozen
10×10 `augmentedJacobian`, whose first nine rows are J and whose last row is the
Kronecker row at coordinate 9.

1. For every perturbation v and every i : Fin 9,
   `(augmentedDerivative v) i.castSucc = (coefficientDerivative v) i`, and
   `(augmentedDerivative v) (Fin.last 9) = v 9`.
   These are derived from the matrix-times-vector definitions, including all ten
   columns. The last identity reduces one finite sum with a single nonzero term;
   the first is a structural row equality, not another numerical Jacobian oracle.
2. The deleted-last-row/deleted-last-column submatrix of A is exactly K.
   The actual last row is zero except for its last entry 1. Hence one Laplace
   expansion along that row gives `det A = (−1)^(9+9) · 1 · det K = −1088 ≠ 0`.
   Only the scalar sign `(−1)^18 = 1` and nonzero integer −1088 need elementary
   evaluation. No 10×10 permutation expansion, new LU factorization, inverse-entry
   computation, or additional interval subdivision is required.
3. The continuous-linear-map determinant of `augmentedDerivative` equals `det A`.
   This must use the real `Matrix.mulVecLin`/`toContinuousLinearMap` wrapper and
   the existing determinant bridge, rather than substitute an unrelated map.
4. Define the actual affine curve γ(t) by the nine constant coordinates
   `coefficients basePoint` followed by the freely prescribed tenth coordinate t.
   Then γ(1) = `augmented basePoint`, because the actual base point's coordinate
   9 equals 1. Coordinatewise continuity proves γ is continuous.
5. A genuine local inverse g supplies a positive **existential** ε for which
   `|t−1| < ε` implies `g(γ(t)) ∈ parameterBox` and
   `augmented (g(γ(t))) = γ(t)`. Extracting the first nine and last coordinate
   equalities gives the exact frozen fiber conclusion.

The existing parameter box radius remains 1/16. We do **not** claim the free
parameter interval has radius 1/16: the inverse-function theorem gives some
positive ε, possibly smaller. Its image must lie in the complete box, not merely
at the base point or in a lower-dimensional subset. No quantitative inverse
radius is needed by the original frozen statement, so computing one would add
work without strengthening the target needed here.

## Contract 12: actual augmented strict derivative

First prove the map-action identities above using the real frozen definitions.
For cast-successor rows use `Fin.lastCases_castSucc`. For the final row use
`Fin.lastCases_last` and the delta-row sum. Do not unfold all 90 Jacobian entries.

Apply `hasStrictFDerivAt_pi'` to the ten-coordinate target. For the first nine
coordinates use the already proved `coefficient_strict_derivative` and identify
the row derivative maps with the structural action identities. For the last
coordinate use `hasStrictFDerivAt_apply` at coordinate 9. Function equality is
the actual `Fin.lastCases` definition; derivative-map equality is proved on
arbitrary perturbation vectors. Use `congr_fderiv` for an equality of maps, not
an assumed derivative table.

Contract 9's dependency gate passed in the coordinator's actual local run 92.
The source-bound receipt and all eight fresh component/assembly logs are retained
and authenticated with this plan, including the accepted earlier seed reuse.
This is an audit of actual coordinator execution, not a fresh run by this author.

## Contract 13: equivalence from the existing exact minor certificate

Use `Matrix.det_succ_row augmentedJacobian (Fin.last 9)` and
`Finset.sum_eq_single (Fin.last 9)`; every omitted term vanishes because the
actual last-row entry is zero. `Fin.succAbove_last` identifies both deleted index
maps with `Fin.castSucc`; the surviving submatrix is the literal `jacobianMinor`.
Reuse `jacobian_minor_nonsingular`, whose proof already consumed all 81 exact LU
entries. Check the resulting scalar sign with a small kernel arithmetic tactic.

The pinned `LinearMap.det_toLin'` and `Matrix.toLin'_apply'` connect this matrix
determinant to the actual derivative map; the finite-dimensional continuous
wrapper is definitionally the same linear map. Then use
`ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero` and its exact coercion
theorem. There is no need to compute an explicit inverse matrix or prove a new
finite-dimensional inverse theorem.

## Contract 14: genuine inverse-function theorem and full-box image

Obtain the continuous linear equivalence from contract 13 and rewrite contract
12's derivative with its exact coercion equality. Apply the pinned strict
inverse-function theorem directly:

- `HasStrictFDerivAt.localInverse` defines g;
- `localInverse_continuousAt` proves continuity at `augmented basePoint`;
- `localInverse_apply_image` gives its exact base-point value;
- `eventually_right_inverse` supplies the genuine right-inverse neighborhood;
- `localInverse_tendsto` transports the open box neighborhood of `basePoint`.

The box neighborhood comes from both halves of the already proved
`parameter_box_geometry`. Conjoin the transported box membership and right
inverse events. No global inverse, injectivity beyond the neighborhood, or
unproved property of an arbitrarily chosen inverse is inserted.
That box theorem already consumes the genuine kernel-mode LeanCert scalar
certificate; no ceremonial duplicate interval calculation is added here.

## Contract 15: continuous free-coordinate slice

Define γ with `Fin.lastCases t (coefficients basePoint)` and prove its coordinate
formulas using the pinned core Fin API. Prove continuity by `continuous_pi` and
last/cast-successor case analysis, using the identity map or a constant in each
coordinate. Establish γ(1) = `augmented basePoint` from the actual base-point
literal; a direct typed conversion avoids the literal-vector simplifier that
previously failed elsewhere.

Pull contract 14's eventual conjunction back along γ at t = 1.
`Metric.eventually_nhds_iff` turns this genuine neighborhood into ε > 0, and
`Real.dist_eq` converts its metric condition to `|t−1| < ε`. Set ψ = g ∘ γ.
For every admissible t, retain full-box membership. Evaluate the actual augmented
right-inverse equality at every cast-successor coordinate to prove equality of
the full nine-coefficient functions, and at `Fin.last 9` to prove `ψ t 9 = t`.
This proves the exact unconditional fiber statement; it does not merely establish
a conditional reduction to an unproved inverse-function hypothesis.

## API and implementation discipline

Primary source hashes and exact excerpts are recorded separately. The relevant
APIs are already present in the pinned local Mathlib and Lean sources. Default
heartbeat and root runner limits stay unchanged. Suggested small modules:
`AugmentedDerivative`, `AugmentedEquivalence`, and `LocalFiber`; splitting is to
reuse completed modules and isolate diagnostics, not to hide missing obligations.

All thirteen protected files, all four public headers, canonical problem identity,
library pins, and the original dimension-nine negation remain unchanged. This
plan contains no Lean implementation for contracts 12–15. The coordinator must
accept it before that code is written. The author runs no Lean, Lake, Comparator,
Git mutation, or network operation. Local proof runs and eventual real Linux
Comparator runs remain separate evidence, and this batch cannot itself count as
a complete solved original target.

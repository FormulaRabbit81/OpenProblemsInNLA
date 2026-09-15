# MF-02 source correspondence and proof route

This is an implementer's source map, not an independent referee verdict or a
claim of a successful final Lean build. The complete source candidate is under
Linux development checking. The original `NUMERICAL_TARGETS.md` and statement
freeze are immutable historical records.

The retained source is the complete MF-02 `solution.md` at upstream commit
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`, SHA-256
`e104a785ddecbec117f6dffe58110222550dd7f1354bfda8c67c37daa68c1924`.
The canonical README at that revision has SHA-256
`b779c356388860ddeab25dc9b6f35d968b6f42625c598038fa402e6841b477c9`.

| Source obligation | Actual implementation | Bridge to the target |
| --- | --- | --- |
| Full real two-interval maximum, Section 1 | `Errors.uniform_error_is_maximum` | Real sign is evaluated on both closed intervals; compact images give a genuine attained maximum and a pointwise bound. |
| Shared-register degree growth, Section 2 | `Model.program_degree_bound` | Induction on actual `ProductHistory`, with arbitrary operands in `freeSpan`, proves degree ≤ 2^m. Free combinations and register reuse are retained. |
| Cubic class degree and cost, Sections 2–3 | `Model.cubic_degree_and_cost` | The actual composition has degree ≤ 3^T and is computed using at most 2T gates, with a square and a shared cube per stage. |
| Chebyshev lower bound, Lemma 1 | `Parity` and `Chebyshev.degree_error_lower_bound` | Symmetrize any p, compress its even square using actual polynomial `contract`/`expand`, map [δ²,1] to [-1,1], and use the imported proved Chebyshev exterior theorem. |
| Complete cubic interval map, Section 3 | `Cubic.optimized_cubic_interval` | Both endpoints and every real interior point are handled by exact nonnegative factors; √A/√3 lies strictly inside the interval. |
| Ratio squaring, Lemma 2 | `Cubic.optimized_cubic_ratio` | Proves positive denominators and square-root identities, then the exact degree-six factorization. |
| Iterated error estimates, equations (7) and (11) | `Iteration`, `Bounds.cubic_error_bounds` | An actual length-T polynomial is constructed. The final centering is absorbed into the last stage, so the upper bound explicitly requires T ≥ 1. |
| Strict decrease of infima, Lemma 3 | `Iteration.cubicError_square_step`, `Bounds.cubic_error_strictly_decreases` | A strict tolerance between C_T and min(1,√C_(T+1)) selects an actual composition with smaller error via the infimum property. No coefficient optimizer is assumed. |
| E_0=E_1=r_δ, Section 5 | `Bounds.unrestricted_error_small_budgets` | Every one-gate output is at most quadratic; its odd part is linear and cannot improve error beyond the linear lower bound. A centered linear polynomial realizes the matching upper bound in the actual program class. |
| Nonempty stage set, equations (14) and endpoint argument | `Minimum.stage_minimum_attained` | An explicit admissible natural stage exists. `Nat.find` then proves the actual `WithTop ℕ` infimum is finite, attained and minimal. |
| T_min(0)=T_min(1)=1 | `Minimum.stage_minimum_small_budgets` | Stage zero is strictly inadmissible and stage one is admissible for both budgets. |
| floor(m/2) ≤ T_min ≤ m, m≥2 | `Minimum.stage_minimum_bounds` | Actual cubic/program inclusion yields E_m≤C_floor(m/2); strict decrease excludes every earlier stage. T=m is explicitly admissible. |
| Full uniform Θ(m+1) theorem | `Minimum.uniform_asymptotic_order` | Natural floor arithmetic, finite attainment and real casts prove constants 1/4 and 1 for every m≥0 and every real 0<δ<1. |

Namespace labels in the table abbreviate files; all public declarations live in
`NLA.MF02`. `Solution.lean` imports only proved helper modules and subjects all
thirteen exports to LeanCert kernel-trust assertions and transitive axiom output.
The separate Challenge module is never imported by the proof.

The source proof's general exterior absolute-value Chebyshev result is stronger
than needed here. The formal proof reverses the affine map, putting the exterior
evaluation point at `(1+δ²)/(1-δ²) ≥ 1`, with a positive value to bound. Mathlib's
proved `eval_iterate_derivative_le_of_forall_abs_le_one` at derivative order zero
is therefore sufficient. The exact Joukowski recurrence avoids logarithm and
cosh calculations. Every interval is treated symbolically; there is no interval
subdivision, mesh, numerical precision choice or trusted numeric estimate.

The original argument separately excludes zero actual error. The formal proof
instead argues by contradiction with any strict tolerance e between the actual
error and the desired positive lower bound. Nonnegativity makes e positive;
the ratio power is strictly below one. This includes actual zero error without
assuming it away and without adding a hypothesis.

The complete canonical asymptotic target is covered. Exact optimal T_min beyond
the two small budgets, an optimal leading constant, the value of E_m, and the
stronger comparison at the same multiplication budget remain outside the source
theorem and these exports. These scope limits must remain in publication metadata.

Mathematical attribution remains: George Stepaniants for the retained expository
proof note, Chen–Chow for the optimized cubic, Cheon–Kim–Kim for prior
constant-factor complexity, and Yuval Filmus for the reused Mathlib Chebyshev
development. Formalization author: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. AI assistance and review roles are disclosed separately; no
contact email, human peer review, official Tau Ceti endorsement or novelty claim
is included.

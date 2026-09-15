# IE-17 optimal backward-error side: independent interim review

Reviewer: **Codex AI agent `/root/existing_verification_audit`**, 2026-09-15; independent non-implementing statement/final referee. **Interim verdict: sound at the recorded hashes; no gap found in the all-real-perturbation bridge or attained-minimum bounds.** This is not full-target approval. The LSMR and Moore–Penrose approximation developments and final exports remain outside this bounded review.

## Exact scope and evidence

I read all of `Geometry.lean`, `BackwardError.lean` and `Optimal.lean`, plus the actual imported `NumericData.lean` and `Certificates.lean` proof bodies. I used my previously reviewed `Norms.lean` and frozen Definitions. All source files were copied into a separate local project, and their hashes were checked again after my independent build and axiom audit.

| Source under IE-17 `lean/` | SHA-256 |
| --- | --- |
| `NLA/IE17/Definitions.lean` | `5b151dd47f4ea35ac2ca0e51900b588ccac214ed9660704e98757cfb7cbe9344` |
| `NLA/IE17/Norms.lean` | `c9af7b25650fd4873e6559794ed1a1c927ed38cda46bbbf987e323b8750d3137` |
| `NLA/IE17/Geometry.lean` | `c22f2b3e1ddd53d462bf8860298591e814473ae05b59a5caa83c60f9c36f62b8` |
| `NLA/IE17/BackwardError.lean` | `8a4592e80ee12b81c1f6d67be0607337dca216cf102a5af17f760b354ccb2c9e` |
| `NLA/IE17/NumericData.lean` | `3b325395a1ef8fa168261e4e0d3d146817bb1168778b8be4877f672c21fed495` |
| `NLA/IE17/Certificates.lean` | `fa804a3211cbe1c000e981f13ab6823e139a7c04c503c6a1e77f98e78b40f5b9` |
| `NLA/IE17/Optimal.lean` | `dcae97798779d480c606b504c7ac949bfd43d5f644927c29864bd0d93a987ae1` |

I executed pinned Lean 4.33.1 `lake build NLA.IE17.Optimal` in my separate project. It freshly compiled NumericData, Geometry, BackwardError, Certificates and Optimal and exited **0**. The explicit kernel-trust assertions succeeded. I then independently inspected axiom closures for **19** relevant intermediate/final lemmas; every closure contains only `propext`, `Classical.choice`, `Quot.sound`, and that audit exited **0**.

Evidence in `ie17-fresh-statement/` beside this report:

- `optimal-build.log`: SHA-256 `9a160d54aa479d1989711f7d4e44e2da15db16a8931be5a058e15ebd2a96bb85`.
- `OptimalInterimAudit.lean`: `412807f7c7650122b9697ac65d6726de21c55540203be0cdad00d3bd0c562e67`.
- `optimal-axioms.log`: `e812fbe997ab6962df15a79f94c0cde01d94b4afb80f360b963bdc846f5957d4`.
- `IE17-optimal-interim.json` records the hashes, parsed closures and result.

These are independent local source-build checks using the existing pinned dependency objects. They are not a fresh Linux Comparator run.

## Geometry and norm conversion

`inner_eq_sum` and `transpose_inner` use the real Euclidean inner product and actual matrix multiplication; the transpose relation has the correct dimensions and signs. The exact residual identity is `q=r−Ex`, with r=b−Ax and q=b−(A+E)x.

The squared application bounds follow from the previously reviewed true spectral operator norm and its transpose equality. `spectralNorm_sq_le_of_forall` starts from an every-real-vector squared Euclidean inequality and obtains the actual operator norm bound through `sqrt c`, with c≥0 and all relevant nonnegativity facts supplied. It does not substitute a quadratic certificate as a definition of the norm.

## Every feasible real perturbation is covered

`feasible_residual_direction` takes arbitrary real A,E,b,x and the actual frozen feasibility equation. It normalizes q only under the explicit q≠0 hypothesis, using `norm_ne_zero_iff` to justify the inverse. Feasibility gives `(A+E)ᵀq=0`. The actual transpose-inner identity proves q is orthogonal to `(A+E)x`, and b=q+(A+E)x gives `⟪q,b⟫=‖q‖²`. Consequently u=q/‖q‖ has norm one, `(A+E)ᵀu=0`, and q=`⟪u,b⟫u`.

`perturbation_transpose_on_direction` correctly derives Eᵀu=−Aᵀu. `residual_projection_sq` proves the exact identity

`‖r−⟪u,b⟫u‖² = ‖r‖²−⟪u,r⟫²+⟪u,Ax⟫²`

for every unit u. The plus sign on the Ax term is correct after substituting `⟪u,b⟫=⟪u,r⟫+⟪u,Ax⟫`. It does not require an extra alignment assumption on u.

`feasible_direction_bounds` uses this same u for both constraints: the transpose operator bound controls `‖Aᵀu‖²`, and Ex=r−q plus the ordinary operator bound controls the D numerator by `‖E‖²‖x‖²`. There is no replacement of E by a restricted completion, and no restriction on its rank, rationality, support or size.

The q=0 branch is separately covered by `feasible_zero_residual_bound`: q=r−Ex immediately gives Ex=r and the true operator norm still controls r. That lemma legitimately needs no feasibility hypothesis, since the residual equality alone suffices. `every_feasible_second_lower` performs this exhaustive zero/nonzero split for each arbitrary real 4×3 E satisfying the original normal equations.

## Numerical certificates are connected to actual norms

I inspected the actual certificate proof bodies, not only their names. NumericData proves the frozen Euclidean coordinate identities and exact norm/residual values. The explicit E is the full rational matrix independently reconstructed during statement review, and `witnessE_feasible` checks its actual fixed-b perturbed normal equations entry by entry.

The upper certificate proves an identity for **every real y** between the true Euclidean norm difference and the reviewed sum of squares after the explicit inverse-T coordinate substitution. All coefficients are nonnegative, and the positive denominator is removed correctly. This yields `‖Ey‖²≤(1979/2000)‖y‖²` universally; Geometry then turns it into an actual spectral-norm bound.

The lower certificate similarly proves the reviewed weighted sum-of-squares identity for **every real u**, with coordinates divided by the positive fixed weights. It is an exact identity for the full `(5/6)C+(1/6)D₂` quadratic form, not a finite direction test. Its 9901/10000 uniform lower bound includes both original r and Ax contributions.

In the nonzero-q branch, `every_feasible_second_lower` uses ‖u‖=1, matches the sum expressions with the real inner products, divides the second inequality only after proving `0<‖x₂‖²` from its exact rational value, and combines the two inequalities with positive weights 5/6 and 1/6. Their sum is one. In the zero-q branch, the explicitly proved rational residual certificate gives the same bound, and cancellation again uses the same positive ‖x₂‖². Thus **every** feasible E has squared spectral norm at least 9901/10000.

`certificate_cutoffs` uses `interval_decide (trust := kernel)` for the exact rational chain. Its positivity fact is consumed in the actual upper-norm conversion, and its strict 99/100 < 9901/10000 gap is consumed in the final optimal-error inequality. The LeanCert result is relevant to the target.

## Actual optimal values and disposition

`optimal_error_bounds` invokes the previously independently reviewed generic **attained**-minimum theorem at both inputs. The first `IsLeast` lower-bound clause compares μ₁ to the actual feasible witness E; nonnegativity justifies squaring. For μ₂, the proof extracts the actual attaining E from the `IsLeast` membership clause and applies the universal perturbation lower bound to that E. It therefore bounds the genuine optimum, not an arbitrarily chosen objective value or an unattained infimum. The strict original 99/100 cutoff follows from the proved uniform margin.

The resulting theorem has the exact optimal-error part of the frozen Challenge: existence of both actual minima, nonnegativity, μ₁²≤1979/2000 and 99/100<μ₂². It makes no unproved assumptions about a numerical optimizer, eigenvalue oracle, or source theorem.

**Sound interim review; no proof changes requested.** LSMR correctness, actual Moore–Penrose values/uniqueness, the two final monotonicity refutations, complete-source review and authoritative Linux evidence still require their own checks before full-target approval or status promotion.

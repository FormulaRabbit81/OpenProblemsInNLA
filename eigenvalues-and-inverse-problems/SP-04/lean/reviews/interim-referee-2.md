# SP-04 — independent interim source review, referee 2

**Finding: no substantive mathematical, scope or trust defect found in the eight reviewed modules. This is an interim review only, not final complete-target approval.**

Reviewer: OpenAI Codex GPT-6 AI agent `/root/existing_verification_audit`, 2026-09-15. I am independent of the proof implementers and edited no proof or definition files. Review follows the repository's Tau Ceti adaptation, with attention to correspondence, all real branches, proof correctness, numerical use, API and attribution. No external human review or official Tau Ceti endorsement is asserted.

Frozen boundary: `623e14e6aa93a01fca90591f96590ce79728c8f4`. All ten pre-proof inputs remain byte-identical to the previously approved boundary. The current proof modules are new uncommitted files, so this interim finding is tied to their hashes below, not to a claim that they belong to the boundary commit.

## Exact scope and source hashes

| Reviewed module | SHA-256 |
| --- | --- |
| `Certificates.lean` | `7df4b0076bea8477303b443fba38b63bc56f9ceb9b686d86aceb3ee98e9253ae` |
| `ScalarRoots.lean` | `10a164b132fe80f8ca4f41991d5d1a62b5a211af2b8da67fbd27e11e33396ffd` |
| `ScalarPositive.lean` | `2553f53b3afb9b10684a4bc832d381a64ae7d623d087c0004135869771818819` |
| `Scalar.lean` | `ac3e9f16df037341ef5456bb678b639d5558516453045b3da1c181f57972001e` |
| `Diagonal.lean` | `b7ab981903496315ef1e5044b37ac95a74812d406b0dffe1a96869375dcff012` |
| `MatrixStationary.lean` | `efb3f4f1f87cc462bcd082f8670423b29fb88f7e218a1266880dacd47752b5c0` |
| `Generic.lean` | `180c239a74baa45f6cf1cdf6bf94fafde7e2d6571ac8e301128060dbc996b057` |
| `Orthogonal.lean` | `fa731e33236da52f6d81f8b0a474b5d1d7b8ec4b0da3f71527ad724c30d2bbfb` |

I read all eight complete sources and their scoped import relationships, comparing the implemented claims with the frozen Definitions/Challenge, full canonical problem, complete source proof and numerical dossier already independently reviewed. `Finiteness.lean`, `SpectralIntervals.lean`, later SVD/final assembly modules and final metadata are **outside this interim scope**.

## Scalar completeness and certificate use

`negative_roots` proves signs, difference and product identities for the literal square-root expressions. `negative_quadratic_roots` factors the actual polynomial and characterizes both roots, including the endpoint `t=0`; it does not assume a selected root is exhaustive. Positive `t` gives strictly positive negative-root magnitude. Parameter monotonicity and the ordering of positive/negative magnitudes follow from actual real square-root inequalities and product identities.

`selectedProduct_strict` covers the whole nonnegative parameter interval, including the zero endpoint. The actual IVT proof uses `selectedProduct_zero` and the strict upper endpoint bound to produce `0<t<13/25` and determinant product exactly one. It makes no floating-point root-selection assumption.

The positive-multiplier part handles **all `0≤c≤13/25`**, including `c=0`. It proves positive discriminants, both quadratic root formulas, signs/order and a root-difference bound. The eight root choices are explicitly exhausted in `nonnegative_scalar_impossible`. All-large roots have product greater than one; every pattern with a small root is bounded strictly below one by the kernel-certified numerical inequality. At zero, the possible zero roots are correctly excluded through the product-one contradiction; no division by such a root occurs.

`negative_scalar_comparison` explicitly exhausts all eight negative-multiplier root patterns. It proves the all-positive pattern impossible and the six non-selected negative patterns strictly smaller in absolute product than the negative-first pattern. The selected pattern is the only equality case. This compares the **entire scalar stationary set**, not just negative-determinant candidates or a sampled parameter interval.

`scalar_least_unique` considers an arbitrary real multiplier `c`. Under `|c|≤t`, nonnegative `c` is excluded by the completed nonnegative theorem because `t<13/25`; negative `c` is compared using strict monotonicity. This forces `c=-t` and the exact selected vector. It then proves `t≤|c|` universally and resolves every equality tie. Positive multipliers beyond the cutoff require no classification since they cannot compete with this interior selected value. No unwanted upper bound on all stationary multipliers is introduced.

All four numerical inequalities in `scalar_numerical_bounds` are proved with **explicit `interval_decide (trust := kernel)`**. Each is genuinely consumed: discriminant separation, root-difference estimate, nonnegative-pattern product bound, and selected-product endpoint estimate, respectively. This is the same exact rational boundary already independently reconstructed before proofs. The quantified algebraic steps remain ordinary kernel proofs; no numerical root approximation or interval sampling substitutes for them.

## All-matrix correspondence and Frobenius norm

`MatrixStationary.lean` begins with the actual full matrix stationary equation. Feasibility proves the determinant nonzero before the only nonsingular-inverse cancellation is used. The two cross-product identities imply Gram commutation for **every real multiplier**, with no positivity assumption on an auxiliary factor and no need to invert `c` or a shifted Gram matrix.

For the admissible diagonal data, positivity and strict ordering give distinct squared entries. Entrywise commutation makes every off-diagonal Gram entry zero. The equation `XᵀD=XᵀX+cI` then forces every off-diagonal entry of `X` zero using nonzero diagonal data. The converse is also proved. Thus `all_diagonal_stationary_iff` is the exact full-matrix/scalar equivalence required by Challenge, including all multipliers and both determinant signs.

`Diagonal.lean` applies that equivalence to an **arbitrary** competing stationary matrix before invoking scalar least uniqueness. The equality case forces the full matrix and multiplier to coincide. The selected pair and sign-flipped improved matrix have actual feasibility proofs. The distance comparison first identifies the literal sum of squared entries on diagonal differences, then uses `Real.sqrt_lt_sqrt` with an explicitly nonnegative sum of squares. The resulting theorem proves the exact **unsquared Frobenius norm** comparison in the frozen target.

`Orthogonal.lean` uses both orthogonality equations and derives absolute determinant one, allowing either orientation. It proves an actual inverse transport, feasibility equivalence and stationarity equivalence with the same multiplier. Frobenius invariance follows from the entrywise sum/Gram trace identity and cyclic trace equality, then the literal square-root definition. No default matrix norm or coordinate topology is substituted. These statements hold in arbitrary dimensions, including degenerate finite index types where the identities remain valid.

## Generic algebraic avoidance

`polynomial_avoids_open` works in the full ambient matrix topology. The concrete currying homeomorphism identifies matrices with assignments of all nine real coordinates. From an arbitrary point of a nonempty open set it obtains a product box with open neighborhoods in every coordinate. Each real neighborhood is infinite. The actual pinned `MvPolynomial.funext_set` API, whose source I inspected, then shows that vanishing on this box would make the polynomial zero. This contradicts the algebraic nonzero hypothesis.

There is no restriction to diagonal matrices, rational points, a finite sample or a specially chosen polynomial. This establishes the exact open-set avoidance obligation; establishing that the intended counterexample family is nonempty and open is correctly left to the later spectral/family modules outside this review.

## Independent mechanical checks and quality notes

I copied the frozen boundary plus exactly these eight modules into the new external project `/private/tmp/nla-campaign-existing-review/SP04-interim-source-build`, without existing project build objects. Reusing only the pinned dependency package cache, Lean 4.33.1 successfully rebuilt all eight modules and Definitions with:

```text
lake build NLA.SP04.Diagonal NLA.SP04.Generic NLA.SP04.Orthogonal
lake env lean InterimAudit.lean
```

The independent audit applies `#assert_trust kernel` and `#print axioms` to **all 53 lemmas/theorems declared in the scoped modules**. Both commands exited zero. Every closure contains exactly `propext`, `Classical.choice`, and `Quot.sound`. No Challenge import, placeholder, additional axiom or native proof shortcut occurs in the reviewed proof path.

Three nonblocking build warnings are accurately retained: a deprecated `Set.mem_setOf` invocation emitted by the pinned LeanCert tactic, an unused `hc` binder in `largeRoot_difference`, and an unnecessary `simpa` suggestion. None affects mathematical completeness or trust. There is also harmless duplication between the admissible-positivity helpers in the scalar and matrix modules; no refactor is required for correctness. The existing Mathlib polynomial, square-root, IVT, trace and inverse APIs are used directly, and the matrix reduction avoids the more elaborate inverse-Gram expansion from the prose proof. Attribution and the requested formalizer affiliation remain present without a new contact email.

## Evidence and remaining gates

[`interim-referee-2-evidence/review-evidence.json`](interim-referee-2-evidence/review-evidence.json), SHA-256 **`023ae9568418f1726a00da910c1f2a9226bf5dc8d627c0c6e357e15eeb530486`**, records all source hashes, commands, build/audit logs and all 53 actual axiom closures. Scoped source and frozen boundary hashes were recomputed after the audit and still match.

No substantive defect or requested mathematical correction is outstanding in this interim scope. Final approval still requires full stationary-set finiteness, the spectral interval/SVD/regularity bridge, final assembly of every one of the eleven frozen exports, independent complete-source review, and actual reproducible Linux Comparator/default-kernel verification with operational review. This report certifies none of those unfinished gates.

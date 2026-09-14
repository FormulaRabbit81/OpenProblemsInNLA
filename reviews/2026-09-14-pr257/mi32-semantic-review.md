# PR #257 — independent MI-32 statement and proof-interface audit

**Verdict: semantic PASS, with one prose correction.** The selected theorem states the entire retained MI-32 upper comparison, without a weakened hypothesis class or an assumed matrix estimate. Correct the fair-sign witness from `M(X) = sqrt n > 0` to `M(X) > 0` (or `2 sqrt n > 0`). Subject to the maintainer's separate authentication of the exact-commit Comparator and NanoDa record, the proposed Lean-verified classification is supported. This audit does not claim a local Lean build, Comparator run, or kernel replay.

## Immutable scope

- Catalog PR head: `cc661b4170e590daeb2ca4232336ab8b6d2eeaaf`.
- Published comparison base: `deb549fa9ddd6b119e6c59016f268237e645dfa2`.
- Formalization: [DiarHaidary/Spectral-norms-of-independent-entries-with-regular-moment-growth](https://github.com/DiarHaidary/Spectral-norms-of-independent-entries-with-regular-moment-growth/tree/762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0), exact commit `762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0`.
- Primary source: Latała–Świątkowski, [arXiv:2106.03139v2](https://arxiv.org/pdf/2106.03139v2), printed pages 24–25, condition (25), Theorem 4.1, and Conjecture 4.3. Both pages were rendered and inspected visually as well as read as text.

The complete canonical `## Statement` section is byte-identical to the published base. Its SHA-256 is `678c57f2122f25ae9682932adafa6f82621d72f9b65119078952ff06a0fa05cd`.

## Statement correspondence

I read `Challenge.lean`, `MI32/Statement.lean`, and `Solution.lean` in full. All eight public definitions agree after removing comments and whitespace; the Challenge imports Mathlib only. The solution's theorem is `MI32.main_upper`, proved through `SymmetricDeletion.exists_upperBoundAt`.

| Requirement | Independent finding |
| --- | --- |
| Original random matrices | Arbitrary type and measurable space, arbitrary probability measure, every integer `n >= 1`, real entries. Joint independence is indexed by original ordered pairs. No symmetry or identical-distribution condition is included. |
| Moments and centering | Every positive real absolute moment is integrable; centering is the genuine integral of each entry. Doubling is required at every real order at least one, exactly as condition (25). |
| Norm and variance | `spectralNorm` is the operator norm on Euclidean coordinate spaces. `varianceScale` adds the finite maximum row and maximum column standard-deviation scales. |
| Weak functional | Deterministic Euclidean unit-ball vectors are quantified outside the scalar moment. Both sums delete the same deterministic original index set. |
| Deletion functional | Outer budgets are exactly `1 <= k <= n`; the inner minimum permits cardinality at most `k`. The exponent is the real natural logarithm of `k + 1`, including `log 2 < 1`. |
| Uniform constant | `C > 0` is quantified before dimension, probability space, and entry laws. The construction is explicitly `deletionConstant (2 * alpha) * exp 1`, so even the universe-polymorphic formulation does not introduce a space-dependent constant. |
| Scope | The formalized claim is the missing upper comparison. The primary paper's Theorem 4.1 supplies the previously known reverse comparison; that reverse result is not part of this Lean target. |

## Vacuity and endpoint checks

I read `WeakMomentBasics`, `StatementChecks`, `RegularWitness`, `DeletionMomentEndpoints`, `CopyDeletionScale`, `GeneralLawCopy`, `MatrixCopySymmetrization`, `SymmetrizationReduction`, and `SymmetricLinearAllOrders` in full.

`WeakMomentBasics` derives a finite moment envelope from the sum of absolute entries for every positive real order. Its weak-test set is nonempty and bounded; the budget-value set is finite and nonempty, with an actual deterministic minimizer. Thus the real supremum/infimum definitions represent the intended extrema. Full deletion yields zero at every positive order, including the `n = 1` endpoint.

Integrability cannot turn the asserted upper bound into a default-zero Bochner-integral statement. Entry integrability follows from the positive-order hypotheses, and `MatrixCopySymmetrization.integrable_operator` obtains operator-valued integrability through a continuous linear map from the finite entry space. `GeneralLawCopy.spectral_mean_le_copy` explicitly includes integrability of both original and copied norms.

For `log 2 <= p < 1`, the copy argument uses subadditivity of the pth power, producing the factor `2^(1/p) <= e`; it does not invoke Minkowski below one. Above one it uses the usual factor two. The exact same original minimizing deletion set is feasible for the copied matrix, so the copy comparison preserves the original budgets and shared-set semantics.

General-law symmetrization is on the actual product probability space: copied entries are `X(omega) - X(omega')`. Independence, symmetry, centering, all positive moments, doubling with parameter `2 alpha`, and the variance multiplier `sqrt 2` are derived. No finite-law replacement occurs. The scalar extension to orders below one uses explicit Hölder interpolation between the half and fourth moments, including a separate zero-second-moment case.

The independent fair-sign witness is nondegenerate and satisfies the hypotheses at `alpha = 1`. Each unscaled entry has second moment one, so its row and column scales are each `sqrt n`. The prose normalization error is in the catalog README line 134 and also in the pinned project's README/source-fidelity prose; `exists_regularEntries` itself asserts only strict positivity and is correct.

## Proof interfaces and limits

I also read the local moment assembly (`LocalSymmetricMoment`, `LocalLogMoment`), nested deterministic selection interfaces, and final five-mask assembly (`SymmetricDeletion`). The local theorem discharges its vacuum-energy estimate through project lemmas, and the final symmetric bound supplies the remaining premise of the general-law reduction. The upper theorem has no unproved comparison as an input. The formal deletion decomposition operates on original rectangular entries; the local bipartite lift is a separate norm-transfer device and does not assert independence of repeated reflected entries.

A fresh static traversal found 113 local modules and 17,955 source lines in the Solution import closure. Challenge is absent. Comment/string-stripped source contains no `sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`, `implemented_by`, or `native_decide` token. External imports are from Lean and Mathlib. This is a source check, not a substitute for checking the elaborated theorem's transitive axioms.

This review checks semantic fidelity, degeneracy risks, the endpoint arguments, and the cited proof interfaces. It does not claim a line-by-line independent analytic reconstruction of all 17,955 lines or human peer review. Exact-commit kernel/Comparator provenance and final catalog integration are separate maintainer checks. Source worktrees remained clean and unchanged.

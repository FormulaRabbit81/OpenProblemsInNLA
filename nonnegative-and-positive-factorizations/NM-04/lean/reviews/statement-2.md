# NM-04 independent statement review

**Verdict: APPROVE the exact statement boundary. No mathematical correction is requested.** This is an independent static mathematical and source review, accompanied by finite exact-rational diagnostics. It is not proof verification, an independent Lean run, official Tau Ceti review, or Comparator execution. The coordinator must accept the two statement reviews and freeze the exact boundary before implementation.

Reviewer: `/root/formal_review_standards`, 17 September 2026. I did not author this NM-04 boundary or its source manuscript. I changed no candidate, source, pin, Git state, or canonical status, and started no Lean process. I applied the retained Tau Ceti correctness, generality, proof-quality, reuse and attribution rubrics to this statement-only phase. Their exact retained text hashes and source locations are in `BINDINGS.json`; I do not assert an unevidenced current upstream Tau Ceti revision or service endorsement.

## Exact reviewed inputs and observed execution

The reviewed snapshot is `next-proofs/NM-04/statement-draft-01` under `/private/tmp/nla-lean-next-20260915`. Its manifest SHA256 is `1797fd8dc2d61041d86d231a8361fe89ac82fb7ab55b2fba5bf45f82451f2c56`. The substantive boundaries are:

| File | SHA256 |
| --- | --- |
| `NLA/NM04/Definitions.lean` | `8f55d605dcd56160feede340a7cb03734be0e04085b4d4bfd30f4d36cede7c6a` |
| `Challenge.lean` | `2e47866aef26d75e14fecc6f569f8c1c7a2812f2bfbd0e47b0c8277ecffc81cc` |
| `NUMERICAL_TARGETS.md` | `40cb823838fa9e68e69909623eaaefae2c91f9a87ed85ebcb63f290453e413e3` |
| `SourceCorrespondence.md` | `927a00174372eb1ba38f56314359f0f5dad1c890c4c29e2bebcea9eadda45478` |
| `comparator.json` | `255a459cccc6b33206dd8bac9b78b5e9a39b73435b7659ef00fffe34fd881495` |

I read the complete canonical [NM-04 target at the bound base](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/849003686970b372e1b2128ba072f86168f81d38/nonnegative-and-positive-factorizations/NM-04/README.md), the complete [Colbrook manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/849003686970b372e1b2128ba072f86168f81d38/references/colbrook-factorization-2026-09-11/manuscripts/NM-04_sinkhorn_identity.tex), all Definitions and 35 Challenge contracts, both mathematical planning documents, comparator list, project guide and draft metadata. The theorem being formalized is the manuscript's Theorem 1 and Sections 1–4. Later extensions are not covered by this verdict.

The independent binding script checked all 13 snapshot entries, all 11 corresponding live files, all 43 pre-code manifest entries and all 37 retained source records. It independently retrieved and verified the three recorded original Git blobs, including the canonical target and complete manuscript; existing source-file records also matched their retained bytes. The manuscript SHA256 is `cc794d1fe11d5ae3bc5eaf1a635720ed0ad5c977cba4c7c7064dc7f29bff0c8f`. This review is bound to that immutable base, not a new claim to have searched all current forks and PRs.

During review, root supplied actual local macOS elaboration run 124. I independently read and checked its original receipt and complete raw logs, retained under `coordinator-run124/`. Definitions exited 0 with no warning; the exact-byte Challenge alias `NM04Challenge` exited 0 with exactly 35 intended `sorry` warnings. Receipt commands specify one thread and 4096 MiB, serially. The source hashes match the reviewed snapshot. Those runs were performed by root, not by this reviewer. They establish statement elaboration, not a proof or an allowed-axiom closure for the intentionally admitted Challenge. No LeanCert certificate or Comparator has run for this draft.

## Complete original target fidelity

The final `rowland_wu_identity` retains every natural dimension `m,n ≥ 1` and every strictly entrywise-positive real `m × n` matrix. It displays the original coefficient sum rather than replacing it with a newly assumed polynomial relation. The row margins are 1 and column margins are **m/n**. The first entry is the actual selected matrix's `(0,0)` coordinate, corresponding to the manuscript's `(1,1)`.

`Index m n` consists of every pair of equal-cardinality finite subsets of the original tail row and column indices. `Finset.orderEmbOfFin` genuinely enumerates in increasing order; `position` counts strictly smaller members and then adds one. The first index is prepended before the ordered tail indices for each bordered minor. `minor` and `delta` use actual `Matrix.det`, and `gamma` is the first entry times the actual unbordered minor.

The diagonal coefficient is computed in integers as `k(m+n)−mn`. The four off-diagonal cases retain the original supports, positions and weights: raising **+m**, lowering **−n**, column exchange **+m**, row exchange **+n**, multiplied by their stated parities. The additional lowering exponent `+1` is exactly the minus sign in the definition. The singleton difference predicates imply the required membership/nonmembership and uniquely determine the exchanged indices; distinct off-diagonal cases cannot overlap. The full contracts independently expose those semantics, rather than requiring a user to assume them.

The final determinant is `det ((m : ℝ)⁻¹ • H[E,E])`: **m⁻¹ is inside the principal determinant**, so the factor is `m⁻|E|`. The `delta` product is over E, the `gamma` product is over its full finite complement, and the first-entry power is `|E|`. Simultaneous row/column enumeration of a principal minor does not introduce a sign. These distinctions match the canonical formula exactly.

## Sinkhorn object, nonvacuity and analytic obligations

`sinkhorn` is a total classical choice from actual positively diagonally scaled balanced matrices, with zero as a fallback when the set is empty. This is acceptable here because the boundary separately requires genuine positive-input existence, matrix uniqueness and `sinkhorn_semantics`. The fallback is not selected on the target domain once those obligations are proved. No desired polynomial root, balanced matrix, minimizer, or scaling-existence oracle occurs as a premise of the final theorem or as an assumed fact in Definitions. The canonical target explicitly gives this unique scaling characterization as equivalent to its Sinkhorn object; convergence of a particular alternating-normalization implementation is neither needed for that characterization nor claimed.

The proposed existence route is substantive. It uses actual finite sums, real exponential/logarithm, the real function-space norm, actual continuity/line derivatives, and an actual attained constrained minimum. For `t` with sum zero, if q is its maximum then q ≥ 0 and `‖t‖∞ ≤ n q`; each row partition is at least `a exp q`, so the potential is at least `m log a + m q`. This implies the deliberately weaker half-coercivity bound. For positive dimensions the coefficient of the norm is positive. Compact-sublevel minimization and derivatives in all zero-mean directions can therefore deliver the stated margins; the sum of the imbalances is zero, excluding an arbitrary common nonzero Lagrange multiplier. The positive row/column factors of `rowNormalized` are proved consequences of positive partitions and exponentials. Uniqueness concerns the scaled matrix, not the nonunique scalar gauge of its factors.

The weaker hypotheses on auxiliary analytic contracts are sound: when `m=0`, the relevant sums, potential and imbalances are zero; no row index can be supplied to the partition contract. When `n=1`, the zero-mean space is the singleton zero vector. The existence and final-target contracts explicitly require both positive dimensions. There is no accidental zero-denominator premise missing on the full target.

## Every proposed export

Names below have the common prefix `NLA.NM04.`. All 35 exactly match `comparator.json`, in order; there are no definition exceptions.

| # | Contract | Static assessment |
| --- | --- | --- |
| 1 | `coercivity_half_certificate` | True exact real inequalities `0 < 1/2 < 1`; intended consumption by the coercivity argument is explicit. No executed certificate is claimed. |
| 2 | `row_partition_positive` | Actual positive finite exp-weighted row sum for `n ≥ 1`. |
| 3 | `potential_continuous` | Actual log-sum-exp potential; positive row sums are sufficient. |
| 4 | `potential_line_derivative` | Actual `HasDerivAt` along every real direction, with the correctly oriented column imbalance. |
| 5 | `zero_mean_coercivity` | Whole unbounded zero-mean space and actual finite-product sup norm; lower-entry bound gives the claimed half coefficient. |
| 6 | `potential_attains_minimum` | Actual existential minimizer over the entire zero-mean space, no supplied candidate or compactness conclusion as a premise. |
| 7 | `potential_minimum_has_margins` | True constrained stationary condition with zero total imbalance; also meaningful when there are no rows. |
| 8 | `positive_balanced_scaling_exists` | Genuine positive rectangular scaling existence for every target input. |
| 9 | `positive_balanced_scaling_unique` | Matrix uniqueness with unrestricted positive-factor gauge. |
| 10 | `sinkhorn_semantics` | Excludes the fallback on positive inputs and identifies all actual positively scaled balanced matrices. |
| 11 | `position_sorted_semantics` | Actual increasing order enumeration gives one-based position. |
| 12 | `empty_minor_values` | Empty determinant is 1; both distinguished empty-index minors equal the first entry. |
| 13 | `H_diagonal` | Exact integer diagonal, with no natural-subtraction truncation. |
| 14 | `H_raising` | Correct new-set positions and m coefficient. |
| 15 | `H_lowering` | Correct old-set positions and extra sign on n. |
| 16 | `H_column_exchange` | Correct old/new column positions and m coefficient. |
| 17 | `H_row_exchange` | Correct old/new row positions and n coefficient. |
| 18 | `H_other` | Zero on every remaining distinct pair, not an omitted case. |
| 19 | `weighted_principal_minor_expansion` | Actual determinant expansion over every finite subset; arbitrary commutative ring, zero weights and empty ambient type retained. |
| 20 | `cofactor_signed_minor_formula` | Actual adjugate transpose indexing and ordered deleted minors; no ambient finiteness or minor invertibility assumption. |
| 21 | `universal_rank_one_update` | Genuine polynomial rank-one determinant identity, including singular/empty minors over any commutative ring. |
| 22 | `universal_bordered_determinant` | Border is `[[V,b],[a,d]]`; actual `a·adj(V)b = d det V − det(border)` with k=0 retained. |
| 23 | `minor_lowering_identity` | Cofactor form in the all-ones direction equals signed lowering. |
| 24 | `minor_column_exchange_identity` | Row-sum outer-product direction gives k times the minor plus column exchange. |
| 25 | `minor_row_exchange_identity` | Column-sum outer-product direction gives k times the minor plus row exchange. |
| 26 | `minor_raising_identity` | Product of row/column sums gives total-entry-sum times the minor minus raising. |
| 27 | `schur_margin_identities` | Actual distinguished scalar Schur tail and all three row/column/total margin identities; m/n is preserved. |
| 28 | `schur_bordered_minor` | Uses only nonzero distinguished scalar pivot, not invertibility of an arbitrary selected minor. |
| 29 | `balanced_minor_relation` | Correct `m·minor(B)` term and all signed transition coefficients. |
| 30 | `weighted_transition_action` | Weight `(n/m)^k` converts the raising factor to n and lowering factor to −m; exchanges keep cardinality. |
| 31 | `balanced_null_vector` | Actual pencil kernel vector, with empty entry 1 and explicit nonzero assertion. |
| 32 | `diagonal_minor_covariance` | Both types of minors acquire the same selected-row/column scaling factor; arbitrary factors, including zero, are allowed. |
| 33 | `diagonal_pencil_covariance` | Right multiplication by the actual diagonal factor matrix, with z held fixed. |
| 34 | `sinkhorn_pencil_singular` | Actual null vector for the original input at its Sinkhorn first entry; strictly positive empty coordinate excludes the zero vector. |
| 35 | `rowland_wu_identity` | Literal full canonical coefficient formula for every strictly positive real rectangular input. |

## Singular, empty and normalization cases

No general minor is divided by anywhere in the determinant/minor argument. The only Schur denominator is the distinguished positive scalar first entry. Generic rank-one, bordered and cofactor identities remain over a commutative ring; the stronger assumptions needed by invertible-only library Schur formulas cannot silently be introduced.

The empty tail minor has determinant 1 and cofactor form zero. The k=0 bordered formula reduces to `0 = d − d`. Empty ambient types in the universal principal-minor expansion produce `1=1`. For a canonical one-row or one-column problem, `Index` still contains the empty pair; it is not an empty indexing set. Its pencil reduces to `a₁₁(1−n x)`, and the balanced first entry is `x=1/n`. Positive rank-one matrices, vanishing higher minors and zero polynomial coefficients are allowed. The source asks for the displayed identity, not for every resulting polynomial to be nonzero or irreducible.

## Reuse, proof feasibility and computations

The retained pinned Mathlib source confirms that `orderEmbOfFin` is an order embedding whose image is the selected finite set; determinants, adjugates and reindexing have their actual library meanings. I inspected the relevant adjugate deletion formula, determinant reindexing and Schur-complement APIs. In particular, the pinned `det_add_vecMulVec` route requires an `IsUnit A.det` hypothesis and even documents the missing generalization. It is not already a proof of contract 21. Singular-valid multilinearity/adjugate or polynomial arguments are still required, just as the numerical and source plans state. This is a real implementation burden, not a statement error or an accepted axiom. Likewise compact minimization and actual exp/log derivative bridges remain to be implemented.

The dimensions remain symbolic; no giant finite matrix enumeration or floating approximation has replaced the theorem. The two rational half inequalities are small exact ground facts. Their simplicity is not a correctness defect; the intended LeanCert use must actually be in kernel mode and consumed in the eventual proof as documented. This review does not demand additional decorative intervals. Actual proof quality, transitive axiom closure and material certificate consumption cannot be approved before implementations exist.

My separately written `independent_diagnostic.py` passed 26 families of exact-rational finite checks: arbitrary small rectangular zero/rank-one/integer matrices, 177 selected-minor instances for each universal minor identity, empty borders, positive balanced matrices of shapes 1×1, 1×3, 3×1, 2×2, 2×3, 3×2 and 3×3, all stated Schur/weight/covariance identities, and the literal full polynomial on known positive scaling orbits. It also checks zero/negative scaling factors where the auxiliary contracts allow them and the elementary zero-mean norm inequality. There were 25,488 assertions, of which 23,028 are repeated support-disjointness checks; this is not 25,488 distinct mathematical results. The 14 balanced cases include repeated uniform cases when a perturbation cannot fit. This diagnostic neither evaluates Lean's classical choice nor proves real exp/log or universal statements. Full inputs and counts are retained in `DIAGNOSTIC.json`.

Two review-tool mistakes were retained transparently: an ad-hoc source-binding parser initially expected the wrong JSON key, and the first diagnostic used a loop name that shadowed its coefficient function. The failed diagnostic source and a labeled shortened transcription of its visible error are retained; its corrected execution has an original captured raw log. Neither failure was a Lean run or a counterexample to a proposed statement. The corrected source-binding script and exact diagnostic both exited 0.

## Attribution, metadata and decision boundary

The code and guide credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, for the proposed formalization, and retain Rowland–Wu attribution for the question and Matthew J. Colbrook attribution for the mathematical solution. No George email is added. The draft v0.4 metadata explicitly says statement-only and no completed target; its pre-elaboration wording is historical to this immutable snapshot. Later progress should be recorded without pretending those original draft claims were a proof. No stronger later manuscript result is claimed.

**Required fixes: none.** This approval covers the exact reviewed mathematical statements and definitions only. Any changed substantive boundary needs corresponding review. It does not open the proof gate by itself, approve a future implementation, increment a completed-target count, or authorize marking the canonical problem Lean verified. Two accepted independent statement reviews and a coordinator freeze, subsequent complete local proofs and final independent reviews, and the actual GitHub Comparator/default-kernel/sandbox checks remain distinct stages.

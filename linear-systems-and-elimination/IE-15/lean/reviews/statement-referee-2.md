# IE-15 independent second statement review

**Verdict: APPROVE the exact mathematical statement boundary identified below.**

Phase: before proof implementation. Date: 2026-09-15. Reviewer: **Codex AI agent `/root/existing_verification_audit`**, acting as the second independent statement referee. I did not implement the definitions, Challenge, numerical dossier, or mathematical proofs, and I did not read the other current referee's report before reaching this verdict. I inspected the source itself, independently checked the analytic argument and rational witnesses, and read the actual successful statement-typecheck log. This is an AI-agent review under the repository's Tau Ceti adaptation, not external human peer review or official Tau Ceti endorsement.

No blocking statement-fidelity, numerical, or attribution finding remains. Approval is limited to these exact bytes; a mathematical change to the definitions or signatures requires renewed review. The eight deliberate Challenge placeholders prove no theorem. This approval does not authorize promotion from **Solved** or replace complete proofs, final independent reviews, fresh Linux Comparator/kernel execution, or permitted-axiom checking.

## 1. Exact reviewed identity

Published base: `c7f399b1694e0a68756e8d060e2a71775c044301`. I compared the canonical README and complete `solution.md` against their Git blobs at that base: both are byte-identical. Their full original target and historical attributions remain present.

| File, relative to this Lean project unless otherwise stated | SHA-256 |
| --- | --- |
| `NUMERICAL_TARGETS.md` | `36a0149348cad5c9e71bc18b506df384d0641470cb70510add53871129ee4546` |
| `NLA/IE15/Definitions.lean` | `8d43a24d1aba8dfd616a66a49463d0bb4bee798c1dd904c2bf7614a5e4bb90ab` |
| `Challenge.lean` | `2193762b8e25272342703e34d8246a4a5901dd0cdb0eec71f30ad97ccf5186b9` |
| `comparator.json` | `5198b3f85a070ce13298ee7af09cfef9984e0a932eb888e62fd4213634893b7a` |
| `lakefile.toml` | `ede3790abea57c69ba1fe6591b1b5d6ff52f17fe9d313ab7c5372359f9422639` |
| `lake-manifest.json` | `870a86a98be8aef373fc3461f690535afbd67d33a44f210c488e65fabe2d9a06` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `../README.md` | `15d158615000f0f121540d2d0bad95487e5d1b4dc26c17a2876ab56c8e0be4d1` |
| `../solution.md` | `abe560be8d00a2a98fb4a11619d5e77926649172fbb07828e747500139e97620` |
| `verification/statement-typecheck.log` | `776008fca2edd032b7e109b30a098530c2e1a926d3324d8cd19d21972377b829` |

The inspected Mathlib checkout is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`; its tracked working files have no Git diff. The manifest pins LeanCert to `621a43d7cf21f87872392a01e874f2f1dbddc926` and all transitive packages to full commit revisions. This is source/pin inspection, not an independent dependency-object rebuild.

## 2. Canonical target correspondence

The canonical target requires both exact constants, for real nonsingular matrices, with every nonzero rook choice and tie allowed and growth over every active entry. The boundary preserves all these requirements:

- `Mat n` is literally `Matrix (Fin n) (Fin n) ℝ`; no alternate field, symmetry, normalization, sign, sparsity, or invertibility assumption has been inserted.
- `growthSet n` quantifies over every such input with the actual determinant nonzero and every `PivotPath n` satisfying `AdmissiblePath`. It does not assume the desired bound, restrict to the witnesses, or encode the conclusion inside a predicate.
- `AdmissiblePivot` separately requires the selected row and column to be active, the pivot to be nonzero, and non-strict absolute-value inequalities across its own active row and column. Thus zero divisors are excluded and all ties are included. The condition is not complete pivoting: entries elsewhere in the active matrix may exceed the pivot.
- `pivotSwap` is exactly the selected row interchange and selected column interchange. Since both selected indices are at least the stage index, these swaps do not bring any previously eliminated index into the active block.
- `schurStep` takes `B i j - (B i k / B k k) * B k j` for the new trailing block. For real numbers this is exactly the canonical Schur-complement formula. Its divisor is the selected nonzero entry because both swaps move that entry to `(k,k)`. The zero padding applies only outside the new active block.
- `trajectory A path 0 = A`, and the growth maximum uses stages `k = 0,...,n-1`, exactly the original active orders `n,...,1`. The post-final zero matrix is not included. `AdmissiblePath` also checks the last one-by-one pivot, so total division cannot add a valid singular termination.
- At each stage, `activeMaxNN` includes every pair of active indices. `growth` then maximizes over every stage, including the initial input. It is not a maximum of pivots alone.

The fixed padded positions are an exact encoding of shrinking active matrices, not an extra mathematical restriction. Restricting the padded stage to indices `k,...,n-1` recovers the current active matrix. Conversely, each canonical row/column choice supplies the corresponding pair of those global indices. The selected swaps followed by restriction give the canonical next active matrix. Arbitrary additional reorderings of the remaining active indices merely relabel later choices and preserve maxima; the canonical problem itself specifies selected interchanges, which the definition directly implements.

`entryMax_semantics` explicitly exposes nonnegativity, an upper bound for every entry, and attainment. Nonsingular positive-order inputs therefore have a positive denominator; the definitions use the true entry maximum rather than a possibly vanishing arbitrary scale. Proofs must establish the determinant/denominator bridge when dividing the all-entry bound. Requiring an admissible nonzero path does not substitute for this bridge.

The two universal upper-bound declarations cover every active entry in orders three and four. Both witness declarations include exact determinants, initial maxima, admissibility and attained growth. `greatest_growth_three` and `greatest_growth_four` assert actual membership and upper-boundedness through `IsGreatest`, making the intended supremum nonempty and bounded. `exact_rook_growth` states the full conjunction `rookGrowthSup 3 = 3 ∧ rookGrowthSup 4 = 14/3`. Thus a proof cannot discharge the advertised package by using a totalized real supremum on an empty or unbounded set.

The single supremum of the set of all admissible growth values is the canonical supremum over all inputs and all their permitted paths. The greatest-element statements prove the required least upper bounds and attained lower examples; no unproved optimizer or numerical supremum is built into this definition.

## 3. Imported meanings and Comparator configuration

I inspected the relevant pinned API definitions, rather than inferring their meaning from theorem names:

- `Matrix.det` in `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` is the usual Leibniz determinant through the alternating row map.
- The matrix notation is the standard finite-entry matrix notation; the declared `Mat 3`/`Mat 4` types give every numeric literal and fraction its real interpretation.
- `Real.norm` in `Mathlib/Analysis/Normed/Group/Real.lean` is defined as absolute value. The nonnegative norm used by `entryMaxNN` therefore carries precisely the desired entry magnitude.
- `Finset.sup` in `Mathlib/Data/Finset/Lattice/Fold.lean` folds lattice supremum from bottom. On nonnegative reals this is finite maximum with zero as bottom, which does not change the maximum of the nonnegative magnitudes. The nonempty positive-order entry sets and stage sets are explicit here.
- The order-bounds definitions make `IsGreatest s a` mean membership plus an upper bound. The real conditionally-complete supremum API has the expected nonempty/bounded obligations; the public greatest-element declarations address them.
- `Equiv.swap` exchanges the two specified indices and fixes all others, including when the indices coincide.

Direct import-file hashes read were: determinant `37646a248748fd65e37c20a21b4a20fea11539d4312aae4f277e4faef8ed2b87`; matrix notation `0a5b11bff151565fa33a4b7faf0e20d4bf2d27075f98f88a0a9e9e25b40e2940`; real norm `eaae958600a11f6a363c1aaf0f5d9d2f85f27a277eb26b6cbfe16e6462922cd4`; finite supremum `79b80dd5aa12886d31c582ab00585627dc4e7f1d7607c7b707484f38d95ce2f4`; conditional supremum `4e4c9abe9993f2334c389d6cb4b75b31b44bb66bb87b65a95b3abac2dbd9fcc8`.

The final inspected Comparator configuration names exactly the eight Challenge declarations, has no replaceable definition holes, uses distinct Challenge/Solution environments and permits only `propext`, `Classical.choice` and `Quot.sound`. `Definitions.lean` imports no solution, tactic or certificate. A future Solution must not import Challenge, directly or transitively.

## 4. Independent exact numerical checks

I wrote and executed a separate standard-library `Fraction` reconstruction rather than rerunning the author's checker. It computed determinants by a permutation-sum formula and elimination by explicit shrinking row/column swaps and Schur updates. The results are retained in [statement-referee-2-exact-checks.json](statement-referee-2-exact-checks.json), SHA-256 `a22455687b09394bb43fa9faaea09c9f43b2ddcc9abcf60da8770e287a6fe275`.

| Witness | Determinant | No-swap pivots | No-swap active maxima | Growth |
| --- | --- | --- | --- | --- |
| Order three | `3` | `1,1,3` | `1,2,3` | `3` |
| Order four | `70/9` | `1,1,5/3,14/3` | `1,2,3,14/3` | `14/3` |

Every intermediate matrix matches the numerical dossier. In particular, the order-four second-elimination active maximum is **3**, while the universal rough bound at that stage is 4; these are correctly distinguished. Every selected no-swap pivot satisfies both rook inequalities with non-strict ties.

As an additional indexing check, I independently enumerated every rook-admissible path on these two inputs, and compared each shrinking-matrix update with a separate padded-global-index implementation: all updates agree. There are 14 complete paths for the order-three witness and 56 for the order-four witness. This confirms that the fixed witnesses allow multiple paths rather than having a single path silently hard-coded. It is a finite semantic check on these inputs, not proof of the universal upper bounds.

## 5. Complete analytic argument and numerical-domain review

I read all five sections of the full solution, including the central scalar lemma, and checked the numerical transcription without treating the dossier's claimed PASS as evidence.

The path normalization moves eventual permutations to the outset and changes only signs/scale, preserving rook tests and all magnitudes. The two sign operations make pivots positive and bottom-row multipliers nonnegative without imposing those conditions on the exported original input. Replacing only the final original diagonal entry by one preserves all earlier pivot rows/columns and increases the final positive pivot; it is used only for the final-pivot upper bound, not to assert that all intermediate entries of the original path changed monotonically.

The order-three contradiction needs signed multipliers `a,b,d,f`, nonnegative bottom-row multipliers and the three original-entry inequalities. The dossier retains those domains. The possibly singular three-by-three submatrix used in order four still has its first two nonzero admissible pivots; a zero final Schur value is handled directly, and a nonzero final value admits the last-row sign normalization. Thus this step does not import nonsingularity of an arbitrary principal submatrix.

For the scalar lemma, `q≤1` uses the uniform bound `h≤4`; `q>1` forces opposite signs for `a,b` and `q≤2`. The positive-`b`, nonpositive-`d₂`, and nonnegative-`d₁` branches each retain their respective original-entry inequality. The final branch `d₁=-v<0<d₂` has `U,V>0` and bounds `q c₂ d₂` by all four quantities `q,U,V,UV/q`. For fixed positive `U,V`, the three regions `q≤min(U,V)`, the middle region, and `q≥max(U,V)` give a nondecreasing continuous expression for `Φ`; the last region has `q²≥UV`. The stated algebraic monotonicity route is valid and can replace differentiation without narrowing any domain. Endpoint/sign equalities are assigned to non-strict branches.

The four-dimensional argument uses the real principal-three-by-three bound to get `W≤2`. The `c₃=0` or `d₃≤0` branch yields a final pivot at most three. Otherwise all multipliers applied to original-entry inequalities are nonnegative. The inner two-variable expression is bilinear, so its minimum on the full square is attained at a corner. The negative minimum is a maximum of affine functions in either outer variable, yielding separate convexity. Two endpoint reductions therefore cover the entire outer square; the four bounds `6,10,10,11` are consistent and the final bound is `1+11/3=14/3`. Earlier maxima `1,2,4` lie below `14/3`. There is no gap from certifying only the final pivot while omitting intermediate entries.

No numerical eigensolver, approximate root, interval subdivision or continuous optimizer is needed for these statements. Exact algebra is sufficient. Any later numerical LeanCert use must be kernel mode and participate in a proved bridge; the current statement review neither requires nor credits a disconnected artificial scalar certificate.

## 6. Typechecking, attribution and remaining gates

I read `verification/statement-typecheck.log`: it reports build success for 1,628 jobs and exactly eight expected warnings at the Challenge declarations. I did not independently rerun that build, and replayed/cached elaboration is not a clean dependency rebuild, Linux sandbox run or mathematical verification. The inspected source contains deliberate placeholders only in the specification environment; proof implementation was absent when I reviewed the boundary.

The header credits **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, and discloses substantial OpenAI Codex assistance. The original resolution belongs to the same mathematical author; the retained canonical README also preserves Matthew J. Colbrook's separate order-five lower bound and the Higham/Edelman–Urschel/Shah–Urschel source context. No contact email has been added to this new boundary. The IE-05 trajectory design is attributed as an adaptation. Publication must retain all that historical material and both original constants as one permanent IE-15 target.

**Final disposition: APPROVE for statement fidelity, full mathematical/numerical scope and the identified imported semantics.** No proof body or catalog promotion is approved by this report. The implementer must prove the eight claims with the reviewed definitions, preserve the complete original target, obtain independent final proof reviews, and authenticate successful fresh Comparator/default-kernel verification and transitive permitted-axiom reports before calling the result Lean verified.

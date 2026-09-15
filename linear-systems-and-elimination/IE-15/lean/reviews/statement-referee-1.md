# IE-15 independent statement referee 1

## Verdict

**APPROVE the pre-proof mathematical statement boundary at the exact hashes below.** No material semantic, scope, numerical-transcription, attribution or API defect was found. This approves these definitions and eight proposed signatures for proof implementation; it is not a proof-completeness review, a successful Comparator run, a permitted-axiom audit of a solution, or permission to promote IE-15 to Lean verified.

- Review date: 2026-09-15.
- Reviewer identity: OpenAI Codex AI subagent `/root/reference_api_review`, independently assigned as statement referee 1. This reviewer did not author the dossier, Definitions or Challenge and implements no proof in this pass. Model identity is the parent-inherited GPT-6 family; no unsupported more specific model/version or human-review claim is made.
- Standards: adversarial semantic faithfulness, scope, reuse, attribution and API review adapted from [TauCetiReview](https://github.com/TauCetiProject/TauCetiReview/tree/603b28011f779bd341d0a08e788498b81542bd7d), particularly `_common.md`, `correctness.md`, `scope.md`, `reuse.md`, `attribution.md` and `generality.md`. The user's permanent-ID and existing-verification preservation rules supersede Tau Ceti's repository-specific compatibility policy.
- Independent preparation: I read the complete original solution and wrote a separate statement checklist before seeing these proposed Lean files. I then reviewed the actual source bytes, rather than accepting the dossier's own verdict.

## Exact reviewed inputs

Paths are relative to `linear-systems-and-elimination/IE-15/lean/`.

| Input | SHA-256 |
|---|---|
| `NUMERICAL_TARGETS.md` | `36a0149348cad5c9e71bc18b506df384d0641470cb70510add53871129ee4546` |
| `Challenge.lean` | `2193762b8e25272342703e34d8246a4a5901dd0cdb0eec71f30ad97ccf5186b9` |
| `NLA/IE15/Definitions.lean` | `8d43a24d1aba8dfd616a66a49463d0bb4bee798c1dd904c2bf7614a5e4bb90ab` |
| `lakefile.toml` | `ede3790abea57c69ba1fe6591b1b5d6ff52f17fe9d313ab7c5372359f9422639` |
| `lake-manifest.json` | `870a86a98be8aef373fc3461f690535afbd67d33a44f210c488e65fabe2d9a06` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The source correspondence was checked against retained canonical files:

| Canonical source | SHA-256 |
|---|---|
| `linear-systems-and-elimination/IE-15/README.md` | `15d158615000f0f121540d2d0bad95487e5d1b4dc26c17a2876ab56c8e0be4d1` |
| `linear-systems-and-elimination/IE-15/solution.md` | `abe560be8d00a2a98fb4a11619d5e77926649172fbb07828e747500139e97620` |

These source hashes agree with `reviews/initial-source-hashes.json`, whose recorded published base is `c7f399b1694e0a68756e8d060e2a71775c044301`. The mathematical input hashes were re-read after the interrupted review resumed; none changed.

## Semantic correspondence

1. **Canonical objects and choices.** `Mat n` is `Matrix (Fin n) (Fin n) ℝ`. `PivotPath n` assigns an independent row/column pair at each of exactly n stages. `AdmissiblePivot` requires both indices to be active, the selected entry to be nonzero, and weak absolute-value inequalities over its entire active row and column. No deterministic search, complete-pivot maximum, strict tie rule, rational restriction or positivity premise appears. Thus choices and ties match the canonical problem.

2. **Actual elimination.** `pivotSwap` uses `Equiv.swap k r` and `Equiv.swap k c`, so the selected entry becomes the diagonal pivot. With active indices at least k, these swaps preserve every already eliminated index. `schurStep` uses the trailing Schur update `B i j - (B i k / B k k) * B k j`; over reals this equals the manuscript's product divided by the pivot. Entries outside the new trailing block are zero padding. `AdmissiblePivot` excludes zero pivots before they are divided by, so total real division does not add admissible zero-pivot paths. `trajectory` begins with A and performs one such update per stage. Relabeling the shrinking active matrix by indices k through n−1 is faithful to the original active-matrix definition; the model does not replace all paths by a preferred diagonal path.

3. **Correct maximum and domain.** `entryMaxNN` takes a finite supremum of all entry nonnegative norms. I inspected the imported pinned Mathlib definition `Real.norm`/`Real.norm_eq_abs`: real norm is absolute value. `Finset.sup` is the finite order supremum, with the standard `sup_le_iff` and `le_sup` semantics. `activeMaxNN` includes exactly indices at least k and inserts only zero for excluded indices. `growth` maximizes over every k in `Fin n`, including k=0 and the final one-by-one active matrix, then divides by the initial entry maximum. The maximum is not restricted to pivots. `growthSet` explicitly requires `A.det ≠ 0` using Mathlib's standard determinant, together with an admissible path. For n=3,4, that determinant condition excludes the zero input and hence a zero initial maximum. The n=0 conventions do not enter the target; `entryMax_semantics` requires `1 ≤ n` before asserting an attained maximum.

4. **Complete target and nonvacuity.** `all_entries_bound_three` and `all_entries_bound_four` quantify over all real nonsingular inputs, all admissible paths and all active entries at every stage. `witness_three` and `witness_four` specify nonzero exact determinants, initial maxima one, admissible no-swap paths and attained growth. `greatest_growth_three` and `greatest_growth_four` assert actual greatest elements of the same growth sets, supplying membership and upper bounds; they prevent reliance on a totalized supremum of an empty or unbounded set. `exact_rook_growth` is the conjunction of both canonical real supremum equalities. No difficult upper bound, normalization, factorization existence or final target has been moved into an assumption. The predicates have concrete proposed witness and consuming theorem obligations in this same Challenge.

5. **Exact numerical transcription.** Both matrix definitions match Section 5 of the solution, including the signs of the order-four first-column and last-column entries and its exact real `1/3` coefficients. The signatures use real `14/3` and `70/9`, avoiding natural-number division. The dossier's A4 stage maxima `1,2,3,14/3` are correct; 4 is only the rough universal third-stage bound. Before seeing the Lean proposal I read and ran the existing `Fraction` witness script: it returned A3 pivots `(1,1,3)`, determinant 3 and growth 3, and A4 pivots `(1,1,5/3,14/3)`, determinant 70/9 and growth 14/3, with each exact active matrix and rook inequality checked. This is arithmetic review evidence, not a Lean proof.

## Imported boundary, reuse and attribution

`Challenge.lean` imports only `NLA.IE15.Definitions`. That module imports five Mathlib modules for the standard determinant, matrix notation, real norm, finite suprema and conditional real supremum. It imports no solution, numerical tactic or project theorem. Lean is pinned to 4.33.1; the manifest pins LeanCert to `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`, with concrete transitive revisions. This review trusts that pinned Mathlib closure; it does not claim to have re-reviewed Mathlib itself.

I compared the retained IE-05 Definitions file and confirmed the credited padded-trajectory/finite-maximum design. The rook-specific extension changes the pivot path to row/column pairs and tests both maxima, while omitting IE-05's unrelated orthogonality, Gram–Schmidt and deterministic partial-pivot machinery. Searches of the pinned Mathlib matrix directory found block-Schur-complement results, but no directly replacing all-rook-path trajectory API. The finite maxima correctly reuse `Finset.sup`. No new proof plumbing or competing general theorem API is being introduced in this pre-proof boundary.

The Definitions header preserves George Stepaniants's original proof attribution, the requested Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, the earlier IE-05 source revision and the AI-assistance disclosure. The dossier retains the Higham and contextual literature attribution. No contact email was added. IE-15 remains one problem containing both dimensions, with its canonical source text, ID and path intact.

## Mechanical evidence and remaining work

The root agent reported successful `lake build Challenge` under pinned Lean 4.33.1. I independently read `verification/statement-typecheck.log` (SHA-256 `776008fca2edd032b7e109b30a098530c2e1a926d3324d8cd19d21972377b829`): it reports a successful 1628-job build and exactly eight warnings for deliberate Challenge proof-body `sorry` placeholders. I did not rerun that build, and this log is not evidence of a completed proof. No solution, kernel replay or Comparator result is approved by this statement review.

The two universal bounds still require the genuine all-path elimination argument, including intermediate entries and the singular-final-value three-by-three submatrix case used by the four-by-four proof. Every later proof must satisfy the kernel-only requirement and the permitted-axiom audit. Final referee review must assess actual proved exports and their dependency closure. Any changed byte of the mathematical dossier, Definitions or Challenge requires a renewed statement review; build/manifest changes require an explicit environment review. Comparator configuration is reviewed separately below when supplied.

```json
{"verdict":"approve","summary":"The reviewed pre-proof definitions and eight signatures faithfully express the complete IE-15 target, including all rook paths, ties, intermediate entries, exact attained witnesses and both real supremum equalities.","findings":[]}
```

## Comparator configuration addendum

Reviewed after the unchanged statement boundary: `comparator.json`, SHA-256 `5198b3f85a070ce13298ee7af09cfef9984e0a932eb888e62fd4213634893b7a`. Its Challenge/Solution modules are separate, its eight theorem names exactly match all eight reviewed signatures (checked by parsing the declaration names), `definition_names` is empty, and permitted axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. Configuration coverage is approved. This is inspection of configuration only; Comparator has not been run on a completed IE-15 solution.

# IE-17 independent final source review — referee 1

**Verdict: APPROVE the complete mathematical source and the independently checked local kernel proof.** No blocking finding remains. This is not approval of a future Linux, sandbox, exporter or Comparator run, and does not itself authorize the status “Lean verified.”

- Date: 2026-09-15.
- Reviewer: OpenAI GPT-6 Codex agent `/root/reference_api_review`, an independent AI referee. I authored no mathematical definitions or proof implementation. My contributions are independent reviews, arithmetic checks and audit harnesses.
- Candidate: `0382f57e2d7da770563cc016b84fa3c89e086931`.
- Protocol: repository [Tau Ceti adaptation](../../../../docs/lean/REVIEW.md); no official Tau Ceti service or external human review is claimed.
- Scope: the complete canonical IE-17 statement, original manuscript, frozen dossier and definitions, all eight public signatures, all ten `NLA/IE17` modules, `Solution.lean`, package configuration, README, metadata and actual local evidence.

## Fidelity and eight-target correspondence

I compared the actual proof path with the preserved canonical README and the complete Colbrook manuscript, and reconfirmed all ten pre-proof frozen input hashes. The final implementation preserves both original monotonicity questions and resolves each separately, using the same successive nonzero iterates. The canonical page remains **Solved** at this review stage, with unchanged ID, path, original statement and attribution.

| Export | Checked mathematical bridge |
| --- | --- |
| `spectralNorm_semantics` | The definition is the continuous-linear-map norm between `EuclideanSpace` spaces. Its characterization quantifies over every real test vector, with a nonnegative bound. The scoped matrix L2 operator norm agrees definitionally; no entrywise or Frobenius norm is substituted. |
| `witness_full_column_rank` | The actual integer 4-by-3 matrix induces an injective real linear map. |
| `exact_lsmr_run` | The exact rational iterates lie in the real Krylov spans. Normal-residual orthogonality extends from generators to arbitrary real span elements. Pythagoras proves global minimization, and injectivity proves uniqueness and hence the minimum-length convention. The run starts at zero, has nonzero normal residual at steps 0–2, and first terminates at step 3. |
| `optimal_errors` | `IsLeast` includes an actual feasible minimizer, and its lower-bound clause ranges over all real matrix perturbations with fixed right-hand side. Generic attainment is proved by compactness of a closed feasible sublevel set containing `-A`. No infimum-attainment assumption is smuggled in. |
| `approximation_values` | The witnessed inverse satisfies all four Penrose equations for the literal seven-by-three stack. Uniqueness of the projected matrix implies uniqueness of the approximation value. The exact squared rational values come from the actual Euclidean projected residual divided by the iterate norm. |
| `terminal_errors_zero` | The third iterate is nonzero and an exact least-squares solution. The zero perturbation attains the optimal error zero, and the approximation follows the canonical exact-solution zero convention. |
| `both_errors_increase` | Nonnegativity justifies passage from squared bounds to strict inequalities. Both chains hold at the same first and second nonzero iterates; every cutoff matches the independently reviewed dossier. |
| `canonical_counterexamples` | Each universal monotonicity proposition is independently contradicted by the complete 4-by-3, three-step run and the actual error witnesses. Neither conclusion is hidden in a custom predicate or assumed as a hypothesis. |

The backward-error lower proof splits every feasible perturbation into zero and nonzero new-residual cases. In the latter, the same normalized residual direction controls both quadratic forms through the true operator norm. The zero-residual case is handled directly by `Ex=r`; it is not omitted. Divisions used for the second-iterate bound have proved positive denominators.

The approximation proof first proves the symbolic Gram identity and positive diagonal denominators for every real stack parameter. It then proves all four Penrose laws and a symbolic Euclidean projection-norm identity, before substituting the exact iterates. A generic uniqueness lemma prevents dependence on a chosen generalized inverse. The auxiliary total function `actualQ` does not replace the canonical relation at zero or at exact termination; the public relation retains its required branches and nonzero-iterate domain.

## Proof quality, computation and generality

I read `NumericData`, `Certificates` and `LSMR` in their exact-byte interim reviews, checked those hashes unchanged here, and read the remaining modules and final assembly directly. The retained interim reports are supporting detail, not the basis for an unexamined final PASS.

The rational upper perturbation is checked against the original perturbed normal equations. The upper congruence and weighted lower dominance are expanded into exact sums of squares over arbitrary real Euclidean vectors. Their bridges to operator norms and all feasible perturbations are explicit. The stronger lower cutoff `9901/10000` implies the original strict `99/100` bound. I reran my independent rational checker: all 42 checks passed, including congruence, weighted dominance, feasibility, iterate data and approximation fractions. These arithmetic checks are review evidence; the Lean proofs establish the results.

The source's large determinant and spectral-completion arguments are replaced by exact algebraic certificates for the same actual matrices. The full target is unchanged. Sparse projection algebra also avoids introducing a general inverse API or an eigenvalue calculation. The LeanCert theorem `certificate_cutoffs` is proved with explicit `interval_decide (trust := kernel)`: its positivity feeds the operator-norm upper bridge, its upper/lower separation feeds the strict lower result, and its middle comparison feeds `both_errors_increase`. Thus its certified inequalities are actually consumed. No floating-point optimizer, native decision procedure, deferred numerical test, custom axiom or proof placeholder occurs in the proof closure.

Generality is appropriate: operator-norm, compactness/attainment, residual-direction and projection-uniqueness lemmas retain their natural arbitrary real finite-dimensional domains; numerical counterexample certificates are specialized to the witness. Rectangular and degenerate inputs are not silently excluded from the generic attainment theorem. The concrete full-column-rank example meets the original unrestricted problem and the stricter assumptions claimed for the witness.

## Reuse, API, naming, placement and documentation

I searched the pinned Mathlib source for Moore–Penrose/pseudoinverse, Krylov and LSMR APIs. The search found only the nonsingular-inverse file's statement that it does not treat pseudoinverses, so a small four-equation relation with a direct witness is justified. Existing Mathlib APIs are reused for Euclidean linear maps and norms, transpose operator-norm equality, compactness/extreme-value attainment, submodule spans and finite-dimensional continuity. The small finite-sum inner-product bridge and explicit sparse algebra are proportionate to this counterexample; a new broad numerical-linear-algebra library would add unnecessary machinery.

Names, namespace and file placement distinguish canonical definitions, generic norm/geometry bridges, exact numeric data, certificates, LSMR, approximation and final exports. Comments explain the crucial residual branches and actual norm semantics. The README states the exact scope, simplifications and remaining gates. Its explicit `lake build Solution` command is necessary and correct: the frozen default target remains `Challenge`, whose eight deliberate placeholders are never imported by `Solution`.

Schiffer and Forsythe are credited as structure/API/checker references at fixed revisions, without claiming their mathematical proof code was copied. The requested formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, without a newly supplied contact email. Original mathematical attribution to Matthew J. Colbrook and the Cambridge affiliation remains intact. The inherited manuscript is preserved, not rewritten. AI assistance, independent agent identity and absence of external human/author endorsement are disclosed. The metadata's source-stage claims and its explicit exclusion of specification placeholders from proof-development sorry counts are truthful for these reviewed bytes.

## Independently executed local checks

I made a separate source snapshot with no project build artifacts copied. Only the existing pinned dependency cache was reused; all ten dependency Git commits match `lake-manifest.json`, and their tracked sources are clean. Compiler: Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, `arm64-apple-darwin24.6.0`.

1. `lake build Challenge` passed, 2379 jobs; only the eight expected specification placeholders were reported.
2. `lake build Solution` passed, 3651 jobs; every project proof module was freshly built.
3. `lake env lean AuditFull.lean` passed. The independent harness copies all eight frozen Challenge types into newly named declarations and assigns the actual exports to them. It also checks 15 substantive intermediate results. All 23 closures passed `#assert_trust kernel`; all transitive axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`.
4. The repository metadata schema and advertised Comparator-coverage validator passed for all eight declarations.
5. My independent exact-fraction checker passed all 42 arithmetic checks again.

See the [execution record](final-referee-1-evidence/execution-record.json), [fresh statement log](final-referee-1-evidence/referee1-challenge-build.log), [fresh proof log](final-referee-1-evidence/referee1-solution-build.log), [independent type/axiom harness](final-referee-1-evidence/AuditFull.lean), [axiom log](final-referee-1-evidence/referee1-axioms.log) and [snapshot hashes](final-referee-1-evidence/snapshot-inputs.json). The project author's logs were inspected as supporting evidence, not substituted for these executions.

These local type assignments are not the Lean4 Comparator. The remaining required gate is an independently audited, provenance-linked Linux run with the actual sandbox, source/export hashes, kernel acceptance, permitted-axiom check, eight Challenge comparisons and required checker controls. Final publication metadata must describe that actual result and both independent reviews. No promotion is approved solely by this source review.

## Exact reviewed bytes

Every candidate and frozen input matched the hash records before the snapshot and again at review sealing. The snapshot record also seals the canonical README, original manuscript, review protocol, freeze record and final input list. The following table records the final candidate bytes; evidence-file hashes are in [SHA256SUMS](final-referee-1-evidence/SHA256SUMS).

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `9a3b525a5925e97778fbdedd5a8b0ac40c28064752deb9c86b633459b545a6e5` |
| `NLA/IE17/Approximation.lean` | `3be2ec256ccd43aa39af538510f3d5a241c042a01325cd6a64667b67419a8afa` |
| `NLA/IE17/BackwardError.lean` | `8a4592e80ee12b81c1f6d67be0607337dca216cf102a5af17f760b354ccb2c9e` |
| `NLA/IE17/Certificates.lean` | `fa804a3211cbe1c000e981f13ab6823e139a7c04c503c6a1e77f98e78b40f5b9` |
| `NLA/IE17/Definitions.lean` | `5b151dd47f4ea35ac2ca0e51900b588ccac214ed9660704e98757cfb7cbe9344` |
| `NLA/IE17/Geometry.lean` | `c22f2b3e1ddd53d462bf8860298591e814473ae05b59a5caa83c60f9c36f62b8` |
| `NLA/IE17/LSMR.lean` | `143c528a8f7c8146edacdf7f67597921ff312aa84b3334cd7e4c67396e678a6b` |
| `NLA/IE17/Norms.lean` | `c9af7b25650fd4873e6559794ed1a1c927ed38cda46bbbf987e323b8750d3137` |
| `NLA/IE17/NumericData.lean` | `3b325395a1ef8fa168261e4e0d3d146817bb1168778b8be4877f672c21fed495` |
| `NLA/IE17/Optimal.lean` | `dcae97798779d480c606b504c7ac949bfd43d5f644927c29864bd0d93a987ae1` |
| `NLA/IE17/Proof.lean` | `9989cfdbaee9173434b76b5919627a91141d4bb492cf85b57ee0cdfdf35e1c68` |
| `NUMERICAL_TARGETS.md` | `6a2f97e065892d1b1311d67f8ed3becccd8d7eb324f894278659f71d4a4b0a9d` |
| `README.md` | `ddcffeb80229fedc11d3306daf3caf97934dec7c15fdaadf8be042458eb77c41` |
| `Solution.lean` | `d305189e2b03335016e3828c172709b3de701c9efcf8f4962f4e41ea9c271007` |
| `comparator.json` | `7a674611023fec397d920eb7caaf951ad830bef470c498086556525260b79fe3` |
| `formalization.yaml` | `4d4b001782e9342436dfa53f80edf921964cdbeb115a8d8204a9ddccd51b7791` |
| `lake-manifest.json` | `f65f6e94b95f1638eac96a967aca5bef1fffecf581189571572c88e34d828c7c` |
| `lakefile.toml` | `aeef3cd6cc700f3039502452436c47e782dd992535750077abadeea55b11939a` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `verification/local-challenge-build.log` | `89c90d9dcd9c72fc0083599ab0ba06a3d4b1d83521fa3d1ae4ec6f3911e57c59` |
| `verification/local-solution-build.log` | `4f3a3ef9fd5cfe2f4c2ea2a1025eaa747e503bdf0f02bce101847952b2a70e3f` |

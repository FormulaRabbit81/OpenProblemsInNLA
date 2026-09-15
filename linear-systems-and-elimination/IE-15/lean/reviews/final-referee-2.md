# IE-15 independent final source and full-target review

**Verdict: PASS for the complete proof source, correspondence with the frozen target, and the reviewed build-configuration change.** Fresh Linux Comparator verification and publication metadata/evidence review remain separate outstanding gates; this report does not claim those have run.

Reviewer: **Codex AI agent `/root/existing_verification_audit`**, 2026-09-15. I was the second independent statement referee and did not implement any mathematical definitions or proof source. I read all active proof files and the complete canonical README and mathematical solution, independently rebuilt every project proof module in a fresh source directory, inspected the actual axiom outputs, and performed independent rational checks of the semantic reductions. I did not rely on the implementer's claimed PASS or read the other final referee's report to reach this verdict. This is an AI-agent review applying the repository's Tau Ceti adaptation, not human peer review or official Tau Ceti endorsement.

## Reviewed identity and evidence

The frozen Definitions, Challenge and Comparator configuration retain their statement-approved hashes:

- Definitions: `8d43a24d1aba8dfd616a66a49463d0bb4bee798c1dd904c2bf7614a5e4bb90ab`.
- Challenge: `2193762b8e25272342703e34d8246a4a5901dd0cdb0eec71f30ad97ccf5186b9`.
- Comparator: `5198b3f85a070ce13298ee7af09cfef9984e0a932eb888e62fd4213634893b7a`.
- Complete proof: `2ddefbb9f31483c448295316b55b6f8a32b8d0d9bbfd0d21610fe1b54fba7e91`.
- Solution entry point: `c1b05e5ead668de2133da70178a632aa69ff2125418cb159a2e597de711291eb`.

[review-evidence.json](final-referee-2-evidence/review-evidence.json) records the exact SHA-256 of **every reviewed project source file**, the toolchain and dependency manifest, and the final Lakefile. All 17 copied source/configuration files were unchanged when checked again after my independent rebuild. The canonical README and complete solution remain the published-base bytes identified in [my statement review](statement-referee-2.md), at base `c7f399b1694e0a68756e8d060e2a71775c044301`.

I approve the single Lakefile change from `defaultTargets = ["Challenge"]` to `defaultTargets = ["Solution"]`. The new SHA-256 is `2dd26d1f3978d85910a8572d3cf0d62ef98f01a82b1d3674117dad62ea2962bb`. Requirements and dependency pins are unchanged. The configuration remains a plain TOML package with no custom preparation script. Both libraries remain separately named; changing the default target does not merge the statement and proof environments.

## Complete-target correspondence

All eight final declaration types agree with the frozen Challenge, modulo whitespace and renaming the unused determinant binder from `hA` to `_hA`. I checked this directly and with a separate signature comparison recorded in the evidence JSON. This comparison is source review, not a substitute for Comparator's actual exported-type and dependency comparison.

The public bounds still quantify over every real nonsingular input and every admissible rook path, with all nonzero choices and ties allowed. Their conclusions bound **every entry of every active matrix**, including the original input. Neither a fixed diagonal path, a normalized input, nor a positive-pivot assumption remains in these public conclusions. The internal stronger bound for any fully admissible path is legitimate: that assumption directly gives a nonzero first pivot and hence a positive initial maximum. The public determinant premise remains exactly as reviewed.

Both rational witness exports prove the original matrix entries, nonzero determinants, initial maximum one, true rook admissibility, and exact growth. The greatest-element proofs explicitly insert these witnesses into the actual `growthSet` and bound every element using the universal entry bounds. The final `sSup` equalities therefore use actual nonempty bounded sets through `IsGreatest.isLUB.csSup_eq`. No totalized empty/unbounded-supremum shortcut, optimizer assumption, or hidden conclusion is present.

## Proof correctness and meaning of the reductions

I inspected Basic, Permutation, Normalization, Coordinates and Reduction in full:

- **Finite maxima and denominators.** `Finset.sup` ranges over every active index pair and stage. The proof of positive `entryMax` uses an actual nonzero first selected pivot. The division in the growth bound uses this strict positivity explicitly. The factor-two stage bound uses actual pivot-column dominance, a nonzero divisor, preservation of active indices under swaps, and triangle/product inequalities.
- **All paths.** The order of composition in `tailPerm` matches the selected interchanges. Future interchanges fix previously eliminated indices. The proved stage identity reindexes each original trajectory by its remaining row and column permutations, and `activeMax_reindex` proves equality of the finite maxima in both directions. `exists_noSwap_representative` thus covers every original path without losing any active entries or ties.
- **Signs and scale.** `unitSign` is always a nonzero unit, including at zero multipliers. `signedScale` covariance is proved for the actual Schur update with all needed nonzero divisors. Its chosen row/column signs make each pivot positive and the selected last-row lower multipliers nonnegative, while retaining every stage entry magnitude divided by the positive initial maximum. It does not silently assume these normalizations on the original matrix.
- **Coordinate bridge.** Lower and upper multipliers are actual Schur entries divided by actual pivots. Their bounds come from the two rook conditions. `entry_prefix_coordinates` is a proved induction reconstructing each original entry as its current residual plus preceding rank-one updates, with explicit active-index conditions.
- **Transport back.** Reduction retains an explicit normalized-final-pivot obligation and a separate bound for earlier stages. The final wrappers discharge both obligations at the correct dimension and constant. At the last stage only the final row/column remains; earlier stages use the factor-two bounds. Thus the argument does not prove only a final-pivot estimate and mistake it for full growth control.

I then read Scalar, FourthScalar and NormalizedBounds, including all actual proof bodies. The signed multiplier domains are preserved. The split at `q≤1`, the sign branches for `b,d₂,d₁`, and the cases `D≤0`/`D>0` cover all endpoints. The final bilinear corner argument applies to the entire unit square by explicit nonnegative corner weights.

Three useful exact simplifications from the informal argument are mathematically sound:

1. `scalar_product_bound` replaces the auxiliary minimum-function monotonicity argument. From `U V ≥ q²xy` and `(2-q)(2-qxy) ≥ 0`, it derives `2q+2qxy ≤ 4+UV` on the full specified domain. No numerical subdivision or differentiability premise is needed.
2. `scalar_two_pivot_cross_bound` obtains the needed cross-term bound directly from the complete scalar inequality when `p+q≥2`, and from individual product bounds otherwise. The proof therefore needs no assumption that the selected principal three-by-three submatrix is nonsingular, or any unchecked principal-submatrix bridge.
3. The normalized final-pivot proofs use the existing original bottom-right entry's upper bound by one in the reconstruction identity. They do not need to modify that entry or assert that such a modification preserves all earlier stages.

The actual first-, second- and third-step coordinate identities feed the scalar bounds; these are not standalone scalar results disconnected from the matrices. The fourth-order scalar proof bounds the full contribution by `11/3`, and the original bottom-right entry adds at most one. The final result is exactly `14/3`.

## Witnesses, LeanCert and trust

Witnesses proves every padded matrix entry at each stage by finite case analysis and exact arithmetic. Its determinants use the actual Mathlib determinant. Rook tests include every active row and column index and non-strict ties. Its maxima are `1,2,3` and `1,2,3,14/3`; notably the order-four second Schur complement has maximum three, while the universal earlier-stage bound is four. These values agree with my independent rational reconstruction retained in the statement review.

The LeanCert certificate `four_le_fourteen_thirds` proves `4≤14/3` with explicit `leancert (trust := kernel)` and file option `leancert.trust "kernel"`. The order-four all-entry proof actually consumes it when comparing the universal earlier-stage bound with the final constant. This is a small relevant certificate; no interval search or native evaluator is needed. The rest of the argument is exact algebra and finite order reasoning.

The active project import graph contains no Challenge import. My source scan found no proof placeholder, custom axiom, `native_decide`, `unsafe`, native implementation override, or foreign declaration in the active project graph. The final module asserts kernel trust for all eight public results and the numerical certificate and prints their axiom closures.

## Checks I executed and their limits

I copied the 17 reviewed project source/configuration files to a fresh directory with no project build artifacts, linked the existing pinned development dependency packages, and executed:

```sh
PATH=/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin:/usr/bin:/bin:/usr/sbin:/sbin lake build Solution
```

This independently rebuilt Definitions, Basic, Permutation, Normalization, Coordinates, Witnesses, Reduction, Scalar, FourthScalar, NormalizedBounds, Proof and Solution and exited **0**. The [raw build log](final-referee-2-evidence/fresh-solution-build.log), SHA-256 `7010fb494a4d4fa438aeacefdc378bf1705820543afb9146cfbeebb68533cb1e`, reports successful compilation and nine axiom reports containing only `propext`, `Classical.choice`, `Quot.sound`. I also directly re-elaborated Reduction and executed the separate [semantic axiom audit](final-referee-2-evidence/SemanticAxiomAudit.lean); all fifteen inspected intermediate closures use only those three standard axioms.

This was a **fresh local project-source build on macOS using pre-existing pinned dependency objects**. It was not a dependency rebuild, fresh Linux sandbox, Comparator run, or independent kernel export/replay. Those authoritative mechanical gates remain required.

My independently written [rational semantic probe](final-referee-2-evidence/check_semantic_reduction.py) checked all complete admissible paths for 64 deterministic/sample inputs of orders one through four: 679 complete paths. Every tested permutation trajectory, active maximum, normalized stage magnitude, pivot sign and lower-multiplier sign agreed. Six inputs had no complete nonzero rook path and contributed no path tests. The [results](final-referee-2-evidence/check_semantic_reduction.json) are explicitly finite diagnostics; the Lean proofs establish the universal identities.

## Reuse, attribution and final disposition

The proof uses standard Mathlib finite maxima, real norms, determinants, permutations, order bounds and exact arithmetic. The local semantic helpers correspond directly to this problem and avoid a hidden shared mathematical assumption. The IE-05 finite-maximum/trajectory design is credited. All new proof headers retain George Stepaniants's name and Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, disclose Codex assistance, and add no contact email. Existing source history, Higham's problem credit and Colbrook's separate order-five contribution must remain in publication.

**PASS for the complete source and exact original-target correspondence at the recorded hashes.** No blocking finding remains in this source-review scope. Do not infer completed Linux verification, metadata truth or publication approval from this verdict. Metadata and retained operational evidence can be reviewed in a dated supplement without changing the reviewed mathematical bytes.

## Candidate metadata supplement — 2026-09-15

**PASS for the candidate-stage README and formalization manifest.** This supplement closes the publication-metadata review mentioned above at the following exact hashes; it does not close the authoritative Linux/Comparator gate.

- `README.md`: `c39c5266389dd685a19ba2ef4f14196c2951f6cf01c3aa315d8d02345199948e`.
- `formalization.yaml`: `fde8b1dc1b7bed55f969313054a31a242f68d7aaff1e65aafde2cfaf812b96fe`.
- Pre-proof freeze record: `8757aee189426980f41c87140008536e4eb26d590f9321b310538060b55c6921`.

I read both documents in full and independently ran the repository's actual v0.4 manifest validator. It exited **0**, reporting **PASS (8 declarations)**. The command, result, hashes and no-email scan are retained in [metadata-review.json](final-referee-2-evidence/metadata-review.json). The initial invocation with system Python could not import `jsonschema`; the recorded successful invocation uses the already-installed audit virtual environment. Schema validation establishes metadata consistency only; the source review above establishes the mathematical claims.

The eight advertised results match the actual complete proof exports and Comparator selection. The zero-sorry statement is true of the proof development and definitions; the README explicitly distinguishes the separate Challenge's eight intentional specification placeholders. The declared axiom closures agree with the actual independently rebuilt proof outputs. The stated tiny LeanCert calculation is used in the real order-four proof. The README accurately identifies the local build's limits and the remaining fresh Linux verification; it does not present the local log as sandbox/Comparator evidence.

The author and affiliation exactly retain **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, with no contact email. Source entries preserve Higham's problem attribution, George Stepaniants's original proof and exact witnesses, Colbrook's distinct order-five contribution, and the IE-05 implementation reuse. Structure/API references to Forsythe and Schiffer are disclosed without attributing this mathematical implementation to those projects. AI implementation/review roles and lack of external human review or endorsement are stated explicitly. The original published-base source links and pre-proof freeze remain historically valid even after integrating later unrelated upstream changes.

The documents were written while final independent reviews were pending and conservatively retain that stage description. Once both reports are sealed, the coordinator should update only this stage wording and link the final reports, while continuing to mark fresh Linux Comparator/kernel verification pending and retaining canonical **Solved** status. That routine evidence update must not imply that this report independently ran Linux verification. Any later **Lean verified** promotion requires retained successful authoritative evidence and its review.

Reviewer: **Codex AI agent `/root/existing_verification_audit`**, independent non-implementing referee. No source-review blocker or metadata blocker remains at the hashes above.

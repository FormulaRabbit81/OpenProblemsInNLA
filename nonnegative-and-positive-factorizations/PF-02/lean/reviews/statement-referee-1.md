# PF-02 independent pre-proof statement review — referee 1

**Verdict: APPROVE this exact mathematical and numerical boundary for proof implementation.** No blocking mismatch remains. This is statement approval, not a completed Lean proof, Linux/Comparator acceptance, or permission to promote the canonical status.

- Date: 2026-09-15.
- Reviewer: OpenAI GPT-6 Codex agent `/root/reference_api_review`, an independent AI referee. I did not author the dossier, definitions, Challenge, or mathematical proof implementation. My contributions are this review and separate audit/diagnostic files.
- Published source base: `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.
- Reviewed scope: the complete canonical PF-02 README, complete original Colbrook manuscript (including the optional extensions), prior source review, final `NUMERICAL_TARGETS.md`, all definitions, nine Challenge signatures, Comparator coverage and exact dependency pins.
- Standard: the repository [Tau Ceti adaptation](../../../../docs/lean/REVIEW.md), covering correctness, scope, proof quality, generality, reuse, API, naming, placement, documentation and attribution. No official Tau Ceti or external human review is asserted.

## Complete-target correspondence

The original universal question retains every natural factor size `k ≥ 3`, every positive row/column count, every entrywise nonnegative real matrix, the ordinary-rank condition `rank M = k(k+1)/2`, and exact real PSD rank `k`. Its orbit quotient is over the full factorization space and the full real general linear group. A size-three counterexample negates that complete universal assertion. The separate manuscript Theorem 4, providing examples in every size, is preserved but is neither required nor claimed by this formal boundary.

`Matrix.rank` is the actual finite-dimensional range rank over ℝ. `IsPSDRank` is `IsLeast` of the set of every positive natural size with a nonempty factorization subtype. It includes actual attainment and excludes every smaller positive size; it is not a supplied-size predicate. The proposed cheaper bound `rank M ≤ k²` suffices to exclude sizes one and two, without changing the exact minimum-three target or assuming the stronger symmetric-dimension theorem.

`FactorTuple` consists of independent row and column families. The subtype requires every factor to be real PSD and every trace equation to hold. It imposes no equality between the families, no positive-definite restriction, and no entrywise positivity restriction on factors. I inspected the imported `Matrix.PosSemidef`: it requires Hermitian symmetry and a nonnegative quadratic form, equivalent to the full vector criterion in finite dimensions. For real matrices this is the required symmetric PSD condition. The two exhibited tuples may set their families equal without restricting the full space.

The nine exports have the correct roles: exact positive integer witness/rank/orientations; both actual positive-definite factorizations; exact minimum PSD size; exact quotient semantics; full-fiber orientation nonvanishing; all-congruence orientation preservation; a continuous surjection onto a discrete two-point space; actual disconnectedness; and negation of the original universal connectedness claim. The comparator configuration lists all nine, with only `propext`, `Classical.choice`, and `Quot.sound` permitted for eventual proofs.

## Quotient, topology and nonvacuity

`Congruent F G` quantifies over one unit of the full square real matrix ring. The same matrix transforms every row factor by `Sᵀ A S`; its actual inverse transforms every column factor by `S⁻¹ B S⁻ᵀ`. Both determinant signs are admitted. The relation has no orthogonal, rational, positive-determinant or normalization restriction.

Raw `Quot` forms the equivalence closure of a relation, so the public `orbit_semantics` equality-iff-single-congruence bridge is essential. It is explicitly required for all dimensions and all tuples, together with the projection's quotient-map property. Reflexivity, symmetry and transitivity of the actual congruence relation must be proved; quotient notation alone will not discharge this obligation.

I inspected the actual imported topology instances and independently elaborated them: matrix topology is the finite function-product topology over the standard real topology; the tuple uses product topology; the factorization uses subtype topology; and `Quot` uses the coinduced topology of `Quot.mk`. These are exactly the canonical Euclidean subspace and quotient topologies. `Bool` has the standard discrete topology. Therefore a continuous surjection onto `Bool` is a genuine disconnectedness certificate, without requiring the orbit quotient to be Hausdorff. It is stronger than showing two inequivalent representatives or the failure of a selected path.

Nonemptiness and nonvacuity are supplied by the two complete explicit factorizations. The two determinant signs are `32` and `-32`. Full ordinary rank forces the coordinate determinant to remain nonzero on every factorization, including ones with singular individual factors and different row/column families. The general real congruence determinant multiplier is `(det S)^4`, positive for every invertible `S`. The intended sign map is thus defined continuously throughout the entire fiber and invariant under every orbit identification.

## Independent exact numerical and symbolic checks

My separately written standard-library checker passed **48 checks**. It imports no repository diagnostic or proof implementation. It reconstructs both six-factor families, all 36 trace products for each family, symmetry and positive principal minors, all twelve universal quadratic-form sum-of-squares identities, the trace coordinate metric, the determinants `8192`, `32`, `-32`, and the sufficient exclusions `1²,2² < 6`.

For the crucial congruence identity I derived the six-by-six coordinate representation directly from `Sᵀ E S` on the six symmetric basis matrices, with all nine entries of `S` independent indeterminates. Exact integer-polynomial determinant expansion equals `(det S)^4`, with 120 collected nonzero monomials. This is an identity check, not sampling. The symmetric trace bilinear identity is checked on a full basis. I also read the dossier author's diagnostic, including its separate fifteen-variable covariance check; I did not infer my result from its claimed PASS.

The proposed computations are proportionate: small exact matrix data, generic algebra and actual topology. The dossier's planned LeanCert kernel certificate `0 < (32 : ℝ)` is mathematically correct and can be consumed by the positive-orientation branch of separator surjectivity. It must actually be consumed in the final proof. Its presence will not replace the quantified algebra/topology proofs or the kernel check of the symbolic determinant identity.

## Reuse, structure, attribution and limits

I checked the pinned Mathlib APIs for true PSD matrices, rank-product/cardinality inequalities, determinant/rank implications, PSD congruence, determinant continuity, quotient maps and quotient lifts. These supply the standard machinery; local definitions are justified for the specific factorization/orbit space and witness. The specialized size-three congruence determinant identity avoids unnecessary representation theory while preserving the complete target. The separation of definitions, specification, numeric dossier and future proof modules is clear; names identify actual mathematical objects.

The dossier accurately distinguishes the full original negative answer from the optional every-size extensions. The original manuscript and canonical page remain unchanged. Requested formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, with no new contact email. Original mathematical credit remains Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Neither attribution is an endorsement claim.

I built `Challenge` in a fresh project snapshot with no project build artifacts copied, using pinned Lean 4.33.1 and the existing pinned dependency cache: **PASS, 2062 jobs**, with exactly nine intentional specification-placeholder warnings. A separate `StatementAudit.lean` run passed and printed the actual instance choices, imported definitions and all nine elaborated public types. Every Challenge axiom closure includes `sorryAx`, as expected: these signatures establish no mathematics. The definitions have no placeholders, and no `Solution.lean` or proof implementation existed at review sealing.

Proof implementation must discharge every target and certificate bridge, followed by independent final source reviews, reproducible Linux verification, real sandboxed Comparator comparisons and permitted-axiom checks. The canonical status remains **Solved**. There is no unresolved mathematical statement change requested by this review.

## Retained evidence and exact input hashes

See [snapshot inputs](statement-referee-1-evidence/snapshot-inputs.json), [execution record](statement-referee-1-evidence/execution-record.json), [fresh Challenge log](statement-referee-1-evidence/referee1-challenge-build.log), [elaboration audit](statement-referee-1-evidence/StatementAudit.lean), [elaborated definitions and instances](statement-referee-1-evidence/referee1-elaborated-boundary.log), [independent arithmetic script](statement-referee-1-evidence/pf02-referee1-arithmetic.py), [all arithmetic results](statement-referee-1-evidence/pf02-referee1-arithmetic.json), and [evidence hashes](statement-referee-1-evidence/SHA256SUMS).

All ten final boundary hashes and the three source-context hashes were checked against actual bytes before the fresh snapshot and again when sealing this report. The complete current manuscript hash is distinct from the historical reviewed-body hash recorded inside it.

| File | SHA-256 |
| --- | --- |
| `NLA/PF02/Definitions.lean` | `2036d380c1881af050bb8fe75328615c405b3745bbdd9bc3c873e7d2c243a2c9` |
| `Challenge.lean` | `3b5cc523ed8c883541d57863eaacb9d0e98115186e11ade3f032ec81fc21dd73` |
| `NUMERICAL_TARGETS.md` | `09431a3f80e272ab8aa0ec616d2d9223eb771bda14512b0926beac7d13ec1695` |
| `comparator.json` | `4b3b915c2a15d6d0af4d025dcb61196c1ed4a5559fd0d3ca5179314b331775c7` |
| `lakefile.toml` | `711f93e05247cf5e744f1283c1bc6e9929436bb4bf452b3875e381bda31994f9` |
| `lake-manifest.json` | `19b43bd134b48c326c0977c6134db0c9a7da9fc89961d20cd303390ac7154eda` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `reviews/initial/independent-exact-check.py` | `2817ccba89d0c7811616eff50ffc1d924dd85b556b1781b51352f2203a9665ec` |
| `reviews/initial/independent-exact-check.json` | `1dd1efb5d958636b49e0d5d4b0230eecf626996e7f564de302a010f2179b9ba4` |
| `reviews/initial/source-hashes.json` | `e8993c2534bd26a1237feb97fc09b69ef0888c57ade9cc7bf987ef1cd3739d0d` |

Source context:

| File | SHA-256 |
| --- | --- |
| `nonnegative-and-positive-factorizations/PF-02/README.md` | `4ef3bba41aca6e2a2c66a8a39e5974b54095b85fba0557c6353c253202aa26c7` |
| `references/colbrook-factorization-2026-09-11/manuscripts/PF-02_disconnected_orbits.tex` | `7e41f64f8495231b9cadd5296daa8fe44790039d3f6e25260cd04be258f3bf65` |
| `references/colbrook-factorization-2026-09-11/verification/reviews/PF-02-review.md` | `abd5969fc2873c10161efc8e94cddc0d2953cf4f18a2aefbcc2513a1383528c7` |

# SP-04 — independent final source referee 2

**Verdict: APPROVE the complete original-target source formalization at the exact candidate below.** No substantive mathematical, correspondence, proof or attribution changes are requested. This is final **source** approval; actual Linux/Comparator verification and independent operational review remain pending. It does not promote canonical status.

Reviewer: OpenAI Codex GPT-6 AI agent `/root/existing_verification_audit`, 2026-09-15. I independently reviewed the pre-proof boundary and contributed no proof or definition code. This report covers fidelity, correctness, proof quality, computation, reuse/API, documentation and attribution under [the repository Tau Ceti adaptation](../../../../docs/lean/REVIEW.md). It is AI-agent review, not external human peer review or an official Tau Ceti review.

## Candidate and exact evidence

- Candidate commit: **`6c351ae4a147efb82a2ede9ebc604de0683105c4`**.
- Current published base: `d8c38a795876b132c90df8d1be8682d3dcde394c`.
- Independently approved pre-proof boundary: `623e14e6aa93a01fca90591f96590ce79728c8f4`.
- Preserved source-reference base: `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.
- [26-input candidate seal](final-source-inputs.json) SHA-256: **`76499435f93c35aa89fba98fa74a2c005fa3092ee769d84e9575f69f83c0ea30`**.
- [Independent evidence record](final-referee-2-evidence/review-evidence.json) SHA-256: **`271501bc85a800605b4dd125586c712ab725eb2f78ce2de721e8dfcc447a6df3`**.

The evidence record lists the exact hashes of all 26 candidate inputs, all ten frozen pre-proof inputs, original source files, relevant pinned Mathlib APIs and every review evidence file. I compared all candidate and frozen input hashes with the current files and actual candidate Git blobs, and rechecked them after the independent build. Every comparison passed. The eight modules already inspected in the [interim source review](interim-referee-2.md) are unchanged; I reviewed every additional module and final assembly. No module is excluded from this final verdict.

Selected identity hashes:

| File | SHA-256 |
| --- | --- |
| `NLA/SP04/Definitions.lean` | `6ec0afd466bfb054b9a46353f37a01e39333259e2579f21ae5fd52b5e9d57161` |
| `Challenge.lean` | `79aa3fe4ce1d75157f153b259660a8abd08cd8f0cecc7d0fad3ebcca0cf98381` |
| `NLA/SP04/Finiteness.lean` | `278f3af2aff968c413e692e6316e0daf93db45f723b6e85b3cc9c8c2c7464204` |
| `NLA/SP04/SpectralIntervals.lean` | `53e11ecdf676d187d8d8fbde221c6fb23e53ee69666af453a515b4328e4afbd2` |
| `NLA/SP04/SVD.lean` | `496614c29dcbd9158b691377ec9906bfb01fc95dd249b05e6cfbb481620d019b` |
| `NLA/SP04/Spectrum.lean` | `3fbbf404e4d3ef4467958b2f1b062b74d2326db3d3425b2bccd4de4495307bde` |
| `NLA/SP04/Witness.lean` | `39ac7159c06d9d54eb2a2a2145bf5880434a410a4cc590640209ad7195f9963b` |
| `NLA/SP04/Proof.lean` | `6f60b9c599b287a05178b30a79f5bc599633093edf31189785ac565784eb3e67` |
| `Solution.lean` | `f02cf91d8fc859d991363d00cfabe555cc958ddf72850422964fd42286d5aa10` |

The complete original canonical README, Markdown/TeX solution and historical review retain their source hashes from the pre-proof dossier and match both the historical-base and current candidate Git objects. The canonical target, permanent ID/path and original mathematical attribution are unchanged. The main-branch integration changes neither these SP-04 source files nor shared verification tooling or the permanent-ID registry.

## Independent verification performed

I copied all candidate source files into a new external project, `/private/tmp/nla-campaign-existing-review/SP04-final-source-build`, with **no existing project build objects**. Only the pinned dependency package cache was reused.

1. Pinned Lean **4.33.1** `lake build Solution Challenge`: exit **0**, every project module rebuilt. Exactly eleven intentional Challenge placeholders are reported; Solution has no proof holes. [Full build log](final-referee-2-evidence/fresh-build.log).
2. Independent [FinalAudit.lean](final-referee-2-evidence/FinalAudit.lean): exit **0**, `#assert_trust kernel` and `#print axioms` for **all 100 project lemmas/theorems**, including all eleven exports. Every closure has exactly **`propext`, `Classical.choice`, `Quot.sound`**, with no unexpected audit output. [Actual output](final-referee-2-evidence/final-audit.log).
3. Matched all eleven final theorem signatures with Challenge after whitespace normalization; names/order exactly match Comparator. [Signature record](final-referee-2-evidence/signature-check.json). This is supplementary source comparison, **not Lean4 Comparator**.
4. Reran my independent exact-rational/permutation-determinant checker, reproducing the pre-proof result byte-for-byte. [Checker](final-referee-2-evidence/referee-independent-arithmetic.py), [result](final-referee-2-evidence/referee-independent-arithmetic.json).
5. Ran the formalization schema and Comparator-coverage validator independently: **PASS, eleven declarations**. [Log](final-referee-2-evidence/manifest-validation.log).
6. Inspected imports and source for placeholder proofs, added axioms and native/unsafe shortcuts. The proof path contains none and never imports Challenge. Checked that each sealed input remains unchanged after these operations.

These are independent local source-build/trust checks. They are not isolated Linux execution, a fresh build of every dependency, or default-kernel replay by Comparator. The retained harmless linter/deprecation warnings do not affect any proof or trust conclusion.

## Complete-target fidelity

The original target concerns every real stationary pair for `|det X|=1`, both determinant signs, the exact equation `Xᵀ(U-X)=cI`, the actual Frobenius distance, algebraic genericity and all dimensions at least two. Those meanings remain literal in the frozen definitions. `UniqueLeastStationary` compares with every real matrix/multiplier pair and forces equality of the pair in an absolute-multiplier tie. `IsNearest` is the direct feasible global-minimizer inequality, so strict feasible improvement disproves it without an unproved infimum convention.

`RegularData` uses nonzero determinant and the actual real Gram-characteristic root multiset's nonduplication. Real Gram matrices are Hermitian and their characteristic polynomials split into the three real eigenvalue factors supplied by Mathlib. The completed `Spectrum` proof additionally identifies the entire root multiset explicitly for admissible SVD data; no nonreal roots or multiplicities are ignored.

The rule being negated allows an arbitrary nonzero polynomial exception in the full `n²` entries, with regularity, full stationary-set finiteness and unique selection as premises. The dimension-three failure theorem proves **every premise** outside **every** nonzero nine-variable polynomial. Any proper real algebraic exception is contained in the zero set of a nonzero defining polynomial, so this negates the complete algebraic-generic universal question. A single diagonal example would be insufficient, but the proof supplies a nonempty open set in the full nine-dimensional matrix space.

## Scalar selection and complete stationary reduction

The unchanged scalar modules were read in full during the interim review and are included in the independent complete build/trust audit. They prove identities for the actual square-root roots, all needed signs, strict parameter monotonicity, and an IVT witness `0<t<13/25` with selected absolute determinant exactly one. Every one of the eight root patterns is accounted for.

For `0≤c≤13/25`, both roots and their ordering are characterized and every pattern is excluded, including zero roots at `c=0`. For negative `c`, the negative-first pattern uniquely maximizes absolute product among nonempty negative-root patterns. `scalar_least_unique` handles an arbitrary real `c`; any competitor with `|c|≤t` is forced to have `c=-t` and the exact selected entries. Larger positive multipliers require no root enumeration because they cannot beat the strictly interior selected value. Both determinant components remain available throughout.

All four rational certificates use explicit LeanCert kernel mode and are consumed respectively in discriminant separation, the root-difference estimate, the product bound and the endpoint existence estimate. The source proof's unnecessary asymptotic observations are omitted without weakening the least-pair conclusion. No approximate root value or sampled interval replaces a real-quantified argument.

`MatrixStationary` derives Gram commutation directly from the full stationary equation. The only inverse cancellation occurs after proving `det X≠0` from feasibility. Distinct positive diagonal data force the Gram matrix diagonal, and the cross equation then forces every off-diagonal entry of `X` zero. This is valid for every multiplier, with no positive-definiteness assumption on a shifted factor. Both directions of the full-matrix/scalar equivalence are proved.

`Diagonal` applies that equivalence to an arbitrary competing matrix, establishes exact uniqueness of the matrix and multiplier, and proves the sign-flipped matrix feasible. It passes from entrywise squared-distance improvement to the **literal unsquared Frobenius norm** using a proved nonnegative sum of squares and `Real.sqrt_lt_sqrt`.

## Full stationary-set finiteness

`Finiteness` constructs genuine matrices over `ℝ[X]` and proves evaluation commutes with the companion tensor and its determinants. Every scalar quadratic solution gives a tensor eigenvector whose `(1,1,1)` coordinate is exactly one, so it is nonzero. Its eigenvalue is the product of the three entries; feasibility gives either `+1` or `-1`. The appropriate `I-K` or `I+K` matrix is singular, proving the actual eliminant vanishes at **every stationary multiplier**.

The implementation uses `det(I-K)det(I+K)`, equivalent to the dossier's `det(K-I)det(K+I)` in dimension eight. It proves nonzeroness efficiently: at zero the tensor is an explicit column-times-row matrix. The existing dimension-changing determinant identities reduce the evaluation to `1-(s₁s₂s₃)²`, which cannot vanish in the source box. There is no assumed resultant contract or expanded coefficient table.

A nonzero univariate polynomial has finitely many real roots. For each multiplier, each scalar entry lies in the finite roots of a nonzero monic quadratic. Finite products and the actual matrix/scalar equivalence bound the entire fiber. `Set.Finite.of_finite_fibers Prod.snd` then proves finiteness of the full matrix/multiplier set. It does not merely certify one branch or a bounded multiplier range. I inspected the actual Mathlib finite-fiber, polynomial-root and determinant identities used here.

## Spectral family, actual SVD and regularity

`SpectralIntervals` proves that the literal determinant expression equals evaluation of the actual Gram characteristic polynomial. The three opposite-sign conditions define an open set through continuous functions in all matrix entries. Exact rational `norm_num` proofs place the original sample in that set. Its six signs agree with my independent values `-,+,+,-,-,+`; only paired product negativity is required.

The IVT proves a real root strictly inside each of the three disjoint positive squared-endpoint intervals. Taking positive square roots gives a strictly ordered admissible triple. In `SVD`, each root is identified with an actual Hermitian Gram eigenvalue using the characteristic factorization. Distinct roots imply an injective assignment to the three eigenvalue indices; finiteness makes that assignment a bijection. **All three eigenvalues are therefore accounted for**, rather than three arbitrarily chosen values being presumed exhaustive.

The existing orthonormal eigenbasis is reordered by that bijection. Defining `P=U Q diag(1/s_i)` gives both actual orthogonality equations and the exact factorization `U=P diag(s) Qᵀ`; every denominator is proved nonzero from admissibility. No SVD-continuity axiom is used. `Spectrum` proves nonzero determinant and rewrites the Gram characteristic polynomial to the diagonal product, whose roots are the distinct `s_i²`. Thus the original regularity premise is established from genuine matrix data.

## Whole-set transport, genericity and final assembly

`Orthogonal` proves determinant feasibility and stationarity equivalences and the literal sum-of-squares/Frobenius norm invariance under arbitrary two-sided real orthogonal transformations of either orientation. `Witness` explicitly constructs both inverse transformations. It compares an arbitrary target stationary pair by pulling it back, so uniqueness includes all matrices and multipliers. It also proves equality of the whole stationary set with the image of the original set, transporting full finiteness. The strict feasible improvement is transported using the actual norm equality.

The helper `selectionFails_of_admissible_svd` has an explicit regularity input; this is discharged by `admissible_svd_regular` in the final proof, not supplied as an unproved generic assumption. Every member of the open family consequently has the full `SelectionFails` witness.

`Generic` uses the actual currying homeomorphism from nine real coordinates to matrices. A nonempty open set contains a product box with infinite real sides; the existing `MvPolynomial.funext_set` theorem rules out a nonzero polynomial vanishing on that box. There is no diagonal-only or rational-only restriction.

All eleven exact final exports are implemented and covered:

| Export | Completed proof obligation |
| --- | --- |
| `numerical_bounds` | All four consumed exact kernel-mode certificates |
| `diagonal_stationary_iff` | Every stationary matrix iff the full scalar equations |
| `diagonal_counterexample` | Every source-box triple, actual unique least pair and strict feasible improvement |
| `diagonal_finite` | Entire stationary-pair set finite |
| `orthogonal_transport` | Full constraint, actual norm and stationary equation in arbitrary dimensions |
| `spectral_family` | Full-space open set, original sample and actual admissible SVD |
| `regular_svd` | Invertibility and genuinely simple Gram spectrum |
| `open_family_counterexamples` | Every family member has all regularity, finiteness, selection and improvement properties |
| `algebraic_avoidance` | Every nonempty full-space open set avoids each proper polynomial zero set |
| `generic_counterexamples` | Full counterexample outside every nonzero nine-variable polynomial |
| `canonical_counterexample` | Negation of the original universal rule by its dimension-three instance |

The final contradiction passes the witnessed regularity, finiteness and unique selection into the supposed generic rule, then contradicts its global distance inequality with the actual improving feasible matrix. No hypothesis is unused to hide a weakened conclusion.

## Reuse, documentation, attribution and final limitations

The proof reuses Mathlib's Hermitian spectral theorem, finite-root/fiber results, determinant identities, traces, IVT and polynomial uniqueness. Problem-specific definitions remain transparent and names are contained in `NLA.SP04`. The companion construction avoids a large resultant expansion, and the spectral reconstruction avoids a general SVD-continuity development. These choices reduce computation while preserving the complete target.

The project README and `formalization.yaml` accurately describe the completed local proof and pending final/operational gates at this candidate stage. They disclose AI assistance and independent-agent review without asserting human endorsement. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, with no new contact email. Matthew J. Colbrook's original proof attribution and the complete historical source remain preserved. The Forsythe/Schiffer references are correctly described as structural/API references rather than sources of the mathematical implementation.

No substantive finding remains from either my earlier statement review or interim review. The source is approved for the exact candidate bytes. Actual Lean4 Comparator correspondence, authoritative reproducible Linux verification, permitted-axiom replay evidence and independent operational reviews remain required before publication as **Lean verified**.

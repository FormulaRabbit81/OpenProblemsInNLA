# SP-04 independent final source review — referee 1

**Verdict: PASS for the complete source and independent local kernel/type/trust checks.**

- Date: 15 September 2026.
- Reviewer: `/root/reference_api_review`, OpenAI GPT-6 Codex, an independent AI agent. I authored no target definitions or implementation proofs and made no changes to them.
- Candidate: `6c351ae4a147efb82a2ede9ebc604de0683105c4`.
- Current published base: `d8c38a795876b132c90df8d1be8682d3dcde394c`.
- Protocol: [repository Tau Ceti adaptation](../../../../docs/lean/REVIEW.md). This covers fidelity/scope, correctness/proof quality, and reuse/API/documentation/attribution; it is not official Tau Ceti review or external human peer review.
- Authoritative isolated Linux verification, actual Lean4 Comparator and their operational reviews remain pending. This report does not promote the canonical status beyond **Solved**.

## Evidence actually inspected and executed

I read the actual complete original canonical README, the full four-section original proof and historical review, all fifteen `NLA/SP04` modules, `Challenge.lean`, `Solution.lean`, dossier, dependency/configuration files and candidate metadata. All 26 sealed candidate inputs match both the current bytes and Git at the candidate. All ten pre-proof inputs match the approved freeze and commit `623e14e6`; both pre-proof reports are unchanged. Original canonical/source files, historical review and permanent registry match both published bases and the candidate. The original 4,714-byte mathematical block still has SHA256 `77b6c6240eab1eab1cd7f9326a95a4bb7455188f951c11718c1b8c07cf691d95`.

I copied the hash-checked candidate into `/private/tmp/nla-sp04-final-referee1` with no existing project build artifacts. Only the pinned dependency cache was shared. All ten dependency checkouts match their manifest commits with clean tracked files. The actual compiler is Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on Darwin/aarch64.

| Independent executed check | Result |
| --- | --- |
| `lake build Challenge` | Success, 2,386 jobs; exactly eleven deliberate specification holes. |
| `lake build Solution` | Success, 3,693 jobs; no proof holes. |
| `lake env lean AuditFull.lean` | Eleven literal frozen signature assignments, 21 substantive auxiliary closure checks, and one nonempty-failure corollary all accepted. |
| Kernel-trust assertions and transitive axiom output in that audit | All 33 closures use only `propext`, `Classical.choice`, `Quot.sound`. |
| Independently authored rational diagnostics | All 49 checks pass, including six exact Gram determinant values, a separately chosen rational stationary sample, both determinant signs, tensor eigenvector/eliminant checks, and a genuinely nondiagonal orthogonal transport. |
| Manifest schema and Comparator coverage | PASS, eleven declarations and no replaceable definition holes. |
| Independent byte/pin/source/log/closure audit | 231 checks pass. |

The retained arithmetic script was written independently before inspecting the author's diagnostic implementation at statement review; I reran it here. Its output deliberately retains its historical pre-proof wording: it supplies exact diagnostics, while the universal proof is independently inspected and compiled in this final review. The local build has four nonblocking linter/deprecation notices, recorded verbatim in the log, with no theorem or trust failure.

All commands, actual output, exact source/dependency hashes and checks are retained in [the evidence directory](final-referee-1-evidence/audit.json), with [its checksum list](final-referee-1-evidence/SHA256SUMS). These local checks are not an actual Comparator run or an isolated Linux reproduction.

## Complete mathematical correspondence

1. **Literal domain and objective.** `Feasible` is absolute determinant one over real matrices and admits both signs. `Stationary` is the full equation `Xᵀ(U-X)=cI`; `stationaryPairs` ranges over every real matrix and real multiplier. `UniqueLeastStationary` compares every pair and equates both the matrix and multiplier on an absolute-value tie. `IsNearest` compares with every feasible matrix. The norm is exactly `sqrt(sum of all entry squares)`, independent of matrix norm instances. None of the definitions embeds the desired conclusion as a hypothesis.

2. **Every stationary matrix is covered.** `MatrixStationary` derives invertibility from feasibility and proves Gram commutation for arbitrary real `c`. Distinct positive diagonal data force off-diagonal Gram entries to vanish. The cross equation and nonzero data entries then force `X` itself to be diagonal. The public equivalence proves both directions with all three scalar quadratics and absolute product one. No sign assumption on the unknown diagonal entries or multiplier is introduced.

3. **All branches, leastness and uniqueness.** The scalar files treat all eight real-root patterns. For `0≤c≤13/25`, exact radicand and root-difference inequalities place the all-large product above one and every other product below one, including the zero-multiplier endpoint. For `c=-t`, the actual positive and negative root magnitudes satisfy their quadratic identities. The selected product is continuous and strictly increasing, starts at zero and exceeds one at `13/25`; the intermediate value theorem constructs a positive interior parameter. Every other nonempty negative pattern has strictly smaller absolute product at the same parameter. `scalar_least_unique` then compares with **arbitrary** real `c`: larger absolute multipliers are harmless, and any candidate of competing size must equal the selected pair. It does not assume every other branch attains a root or rely on the source's unnecessary asymptotic observation.

4. **Actual strict distance improvement.** Changing the selected first entry from negative magnitude to positive magnitude gives a feasible determinant-sign flip and strictly decreases the entry-square sum by the positive scalar expression. `Diagonal` applies `Real.sqrt_lt_sqrt` with nonnegativity proved for the full sum. The exported strict inequality is the original unsquared Frobenius inequality. The improved matrix is allowed to be nonstationary, as the canonical nearestness question requires only feasibility.

5. **Finite full stationary set.** `Finiteness` forms the actual polynomial matrix tensor product of the three 2×2 companions; `TensorIndex` has eight elements. Every quadratic solution supplies a tensor eigenvector with last entry one. Product ±1 makes one of `det(I-K)` and `det(I+K)` zero, so **every** stationary multiplier is a root of their polynomial product. At zero, the actual matrix is a column times a basis row; Mathlib's determinant interchange identity reduces the determinant to `1-(s₀s₁s₂)²`, which is nonzero on the full original box. This rank-one argument is a valid simplification of the dossier's triangular calculation. Nonzero polynomial roots are finite, and each fixed multiplier has finitely many three-quadratic tuples. Finite fibers and the full matrix equivalence prove finiteness without a bounded multiplier search or an assumed candidate list.

6. **Both orientations and complete transport.** `Orthogonal` proves two-sided inverse transport, absolute determinant preservation, the literal norm through the trace identity, and stationary equivalence. `Witness` proves equality of the whole stationary sets under the action, transports full finiteness, and pulls an arbitrary competitor back before applying uniqueness. Both determinant orientations of both orthogonal factors are allowed. The proof covers every actual admissible SVD, not only the displayed open subset.

7. **Real roots, true SVD, simple spectrum and nonvacuity.** `counterexampleFamily` consists solely of three strict products of actual Gram determinant values and is open in the full matrix topology. The unchanged rational sample proves nonemptiness. Continuity and the intermediate value theorem give actual real Gram characteristic roots in three disjoint positive intervals. Mathlib's Hermitian spectral theorem supplies the actual orthonormal eigenbasis and characteristic factorization. The three distinct roots choose distinct eigenvalue indices, hence a bijection of all three indices; reordering the basis and normalizing `UQ` constructs `P`, with both orthogonality equations and `U=P diag(s) Qᵀ` proved. Positivity and interval separation give the full original admissible scalar box. `Spectrum` then proves invertibility and actual `roots.Nodup` from the characteristic product; no possibly incomplete real-root list is used to conceal nonreal roots.

8. **Full algebraic genericity and the original negation.** `Generic` uses `Homeomorph.piCurry` on all `Fin 3 × Fin 3` coordinates, obtains an ambient open box with infinite real sides, and applies the actual `MvPolynomial.funext_set` theorem. Thus every nonzero polynomial in all nine entries leaves a witness in the nonempty open family. Every such witness has proved regularity, full finiteness, unique selection and strict improvement. Any proper real algebraic exceptional set is contained in the zero set of a nonzero defining polynomial, so this defeats the original algebraic qualifier. The final proof instantiates the purported all-dimensions rule at three and contradicts its global nearestness inequality. The audit also derives an actual nonempty failure witness using the polynomial one. No generic-domain premise is left vacuous.

## Computation, reuse and presentation

The four LeanCert goals run with explicit `trust := kernel`. All four resulting conjunction components are genuinely consumed: radicand separation, the algebraic root-difference coefficient, the product bound, and the endpoint needed for existence. They reach the complete canonical theorem through the scalar proof. No floating-point approximation, native axiom, interval subdivision, derivative estimate or expanded 8×8 determinant is needed. The exact rational constants agree with the reviewed dossier and independent diagnostics.

I inspected the pinned Mathlib source for real Hermitian spectral decomposition and characteristic roots, multivariate polynomial uniqueness on infinite boxes, polynomial root finiteness, actual matrix topology, and the determinant interchange identities. The code uses these existing results rather than assuming an SVD or introducing a new polynomial/linear-algebra foundation. The small companion definitions are problem-local and their tensor eigenvector and evaluation bridges are proved; direct finite indices are reasonable for this fixed three-coordinate construction. General orthogonal transport is correctly stated for arbitrary finite dimension. Module placement, names and documentation make the scalar, matrix, finite-set and genericity bridges reviewable. The four small linter notices do not justify changing frozen mathematical bytes.

The README and metadata accurately describe this candidate's local stage and pending operational gates. George Stepaniants's requested full Caltech affiliation is present, with no new contact email. Original mathematical authorship and the complete original source, including its historical attribution, remain preserved. Baaijens and Draisma retain the original question/framework credit. Substantial AI assistance, separate implementing and reviewing agents, and the pinned Forsythe/Schiffer structure/API references are disclosed without claiming independent human endorsement or novelty.

## Exact reviewed candidate hashes

The following table seals the complete candidate reviewed here. The ten separately frozen statement hashes, source-context hashes, compiler and all ten dependency commits are also recorded in `audit.json`; all agree with their authoritative Git snapshots.

| Project-relative input | SHA256 |
| --- | --- |
| `Challenge.lean` | `79aa3fe4ce1d75157f153b259660a8abd08cd8f0cecc7d0fad3ebcca0cf98381` |
| `NLA/SP04/Certificates.lean` | `7df4b0076bea8477303b443fba38b63bc56f9ceb9b686d86aceb3ee98e9253ae` |
| `NLA/SP04/Definitions.lean` | `6ec0afd466bfb054b9a46353f37a01e39333259e2579f21ae5fd52b5e9d57161` |
| `NLA/SP04/Diagonal.lean` | `b7ab981903496315ef1e5044b37ac95a74812d406b0dffe1a96869375dcff012` |
| `NLA/SP04/Finiteness.lean` | `278f3af2aff968c413e692e6316e0daf93db45f723b6e85b3cc9c8c2c7464204` |
| `NLA/SP04/Generic.lean` | `180c239a74baa45f6cf1cdf6bf94fafde7e2d6571ac8e301128060dbc996b057` |
| `NLA/SP04/MatrixStationary.lean` | `efb3f4f1f87cc462bcd082f8670423b29fb88f7e218a1266880dacd47752b5c0` |
| `NLA/SP04/Orthogonal.lean` | `fa731e33236da52f6d81f8b0a474b5d1d7b8ec4b0da3f71527ad724c30d2bbfb` |
| `NLA/SP04/Proof.lean` | `6f60b9c599b287a05178b30a79f5bc599633093edf31189785ac565784eb3e67` |
| `NLA/SP04/SVD.lean` | `496614c29dcbd9158b691377ec9906bfb01fc95dd249b05e6cfbb481620d019b` |
| `NLA/SP04/Scalar.lean` | `ac3e9f16df037341ef5456bb678b639d5558516453045b3da1c181f57972001e` |
| `NLA/SP04/ScalarPositive.lean` | `2553f53b3afb9b10684a4bc832d381a64ae7d623d087c0004135869771818819` |
| `NLA/SP04/ScalarRoots.lean` | `10a164b132fe80f8ca4f41991d5d1a62b5a211af2b8da67fbd27e11e33396ffd` |
| `NLA/SP04/SpectralIntervals.lean` | `53e11ecdf676d187d8d8fbde221c6fb23e53ee69666af453a515b4328e4afbd2` |
| `NLA/SP04/Spectrum.lean` | `3fbbf404e4d3ef4467958b2f1b062b74d2326db3d3425b2bccd4de4495307bde` |
| `NLA/SP04/Witness.lean` | `39ac7159c06d9d54eb2a2a2145bf5880434a410a4cc590640209ad7195f9963b` |
| `NUMERICAL_TARGETS.md` | `e14351bfa611bf6f1d1c7302b0584866bb54074c9db3c1e8f43c1f5dee571290` |
| `README.md` | `20a0f8b1b45f5473828640e673d00290003dd5d5aceaed0980c0f6195ad87974` |
| `Solution.lean` | `f02cf91d8fc859d991363d00cfabe555cc958ddf72850422964fd42286d5aa10` |
| `comparator.json` | `d0783ec075a831cee2a501a46e02e42258b995f9fbf377dab1c749bba95457ff` |
| `formalization.yaml` | `30f2b9f545acbe1a2bbb683ff7f074bff7c007af4286fb5485352ef5bef47555` |
| `lake-manifest.json` | `0b777416633b6ab6cecb4b739da1148251ec285a20225da94da6f72b56bddcab` |
| `lakefile.toml` | `1f4038f5e6c2f3ed9409d51f444f1ca2256b03a828d69b0dca855f61f2b082fd` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `verification/local-challenge-build.log` | `0181b90fc5305c279f076bd279fcab8622eb3a5d82e19a8a89f14c218a11b9a3` |
| `verification/local-solution-build.log` | `27ee5190d06e69c079eec222d1c7719942da03c11e488b98b782c348e07edc2a` |

Evidence checksum-list SHA256: `60657fa848d543be35a39fa4aa2bccaf4dceb83b45add32cbf5e768bd444c89f`.  
Independent audit JSON SHA256: `999b6ecdfc97b4da75e40e7005732e5231f8a80b662d28a7e68ac2ac9157e116`.

**Disposition:** no material correction requested. Approve these exact bytes for the next authoritative Linux/Comparator stage. Promotion to Lean verified requires the separately observed successful operational gates and their independent reviews.

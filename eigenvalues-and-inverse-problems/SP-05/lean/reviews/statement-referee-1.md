# SP-05 independent pre-proof statement review — referee 1

**Verdict: APPROVE the exact ten boundary inputs below. No proof implementation or completed verification is approved by this report.**

- Date: 15 September 2026.
- Reviewer: `/root/reference_api_review`, OpenAI GPT-6 Codex, independent non-implementing AI agent. I did not author or edit the proposed target, definitions, dossier, contributor diagnostics, or proof code.
- Published source base: `d8c38a795876b132c90df8d1be8682d3dcde394c`.
- Protocol: [repository adaptation of Tau Ceti review](../../../../docs/lean/REVIEW.md); fidelity, scope, mathematical correctness, computation, reuse/API, documentation and attribution are covered here at statement stage.

## Material read and independent checks

I read the complete canonical page, all three source-proof sections, historical independent review, complete dossier, actual definitions, all six Challenge signatures, Comparator configuration, pins, retained diagnostic source/output and API probe. The seven canonical/source/review files are unchanged from the published base. The original normalized mathematical block remains 3,483 bytes with SHA256 `54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42`. The complete 217-ID registry and SP-05's canonical path remain unchanged; canonical status is **Solved**.

I copied all ten hash-checked boundary files to a fresh scratch project with no existing project artifacts. Only the dependency cache was shared; all ten package checkouts match their manifest commits and have clean tracked files. The actual compiler is Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on Darwin/aarch64.

| Independent executed check | Result |
| --- | --- |
| `lake build Challenge` in the fresh snapshot | Success, 2,710 jobs; exactly six intended specification holes. |
| `lake env lean BoundaryAudit.lean` | Success; prints actual semantic definitions and all six signatures, checks pinned APIs and real/complex Euclidean instances. The probe contains no implementation theorem. |
| `python3 independent-exact.py` | 177 exact rational/Gaussian-rational diagnostics pass. |
| Independent hash/source/pin/stage audit | All 69 checks pass. |

The source, actual output and checks are retained in [statement-referee-1-evidence](statement-referee-1-evidence/audit.json), sealed by [SHA256SUMS](statement-referee-1-evidence/SHA256SUMS). My diagnostic was authored independently before reading the contributor's diagnostic implementation; it does not import or execute that checker. The subsequent source comparison confirmed the contributor's limited diagnostic claims and deterministic data. No floating-point eigenvalue computation is used.

## Literal statement fidelity and nonvacuity

**Inputs and dimensions.** `Mat n` is the complete real matrix space, and `Matrix.PosDef` actually includes Hermitian symmetry and strict positivity on every nonzero finitely supported vector. On finite real indices this is precisely symmetric positive definiteness. No commutativity, common eigenbasis, simple eigenvalue, even dimension, rational-entry, or minimizing-matrix invertibility assumption appears. The original comparison covers every n≥2. The stronger PSD-eigenmatrix result covers every n≥1; excluding n=0 is necessary for a nonzero eigenmatrix and does not alter the original target.

**Column vectorization and tensor convention.** I inspected Mathlib's `Matrix.vec` definition: `vec X (column,row)=X row column`. Its bijection and zero-reflection facts show that the product index represents the entire n²-dimensional real vector space. `commutationMatrix` is the actual swap permutation matrix. The first export correctly states `(A⊗B) vec X = vec(B X Aᵀ)` for arbitrary real A,B,X, so the Jordan sum represents `AXB+BXA` when inputs are symmetric. Its second and third clauses identify actual transposition and the complete Euclidean dot-product denominator with the Frobenius square. This universal infrastructure also makes sense at n=0 and n=1.

**Real quotient, full sectors and attained minima.** `rayleigh` is the literal quotient `vᵀKv/vᵀv`, and `sectorValues` ranges over all nonzero real vectors satisfying the actual permutation equation. Its nonzero guard makes the denominator positive. `IsLeast S a` is definitionally membership together with a lower bound; therefore it supplies a genuine minimizing vector and compares against every vector in that sector. Both `sector_minima` and `canonical_result` assert attainment rather than assuming it. The latter is exactly the two minima and their inequality in the complete canonical statement.

**Stronger eigenmatrix target.** `positive_minimizer` gives a real, PSD, nonzero matrix, a strictly positive real eigenvalue and the actual Jordan matrix eigen-equation, together with a lower bound against every nonzero real vector. Column-vector injectivity and the positive dot-product denominator make its own Rayleigh value equal to μ. Thus this is an attained global minimum, not merely a lower bound or an eigenmatrix on an assumed preferred subspace. Positive semidefiniteness includes symmetry but allows a singular minimizing matrix and repeated extremal eigenvalues.

**No empty-sector shortcut.** The explicit skew matrix has exactly two nonzero entries whenever n≥2; their squares sum to two and its transpose is its negative. For n=0 or n=1 it is zero, correctly excluded by the skew-witness hypothesis. The symmetric sector has the identity witness when n≥1. The proposed Euclidean unit-sphere intersection argument supplies compact, nonempty feasible sets, continuous quadratic forms, and normalization back to the full quotient sets. These are future proof obligations, not premises hidden in the signatures.

## Mathematical proof plan independently assessed

The source proof and the proposed integral-free replacement are mathematically valid for this full scope.

1. The Jordan operator and its real/complex inverse must be proved self-adjoint and positive definite on the actual Frobenius/Euclidean space. The real coefficients, complex-linear extension, true inverse identities, and transpose/adjoint commutation cannot be supplied merely by choosing notation for an inverse.
2. For a Hermitian PSD right-hand side, inverse uniqueness first makes the solution Hermitian. Congruence by the positive square root of B then gives `C X̃ + X̃ C = Ỹ` with C positive definite and Ỹ PSD. If X̃ had a negative eigenvalue λ and eigenvector v, Hermitian symmetry gives `Re(v*Ỹv)=2λ Re(v*Cv)<0`, a contradiction. This uses the complete **complex Hermitian** cone and does not require C and X̃ to commute. Inverse congruence then gives the required complex PSD-preserving inverse. This replaces the source integral without weakening the property used afterward.
3. A real eigenmatrix for the top inverse eigenvalue has a nonzero symmetric or skew part; degeneracy of that eigenvalue is harmless. Multiplication of the skew part by i supplies a Hermitian eigenmatrix. The positive/negative spectral parts produce the exact quadratic-form difference `4 tr(P Φ(N))≥0`, using self-adjointness and complex PSD preservation. Positivity of the trace needs a PSD congruence argument, not commutativity of P and Φ(N).
4. Equality of Frobenius norms must be proved through the trace/square identities. `CFC.norm_abs` would concern a different matrix norm and is insufficient. Realness of the modulus is also mandatory: for real skew W, `(iW)²=WᵀW`, and real/complex PSD square-root uniqueness identifies its modulus with the complexification of a real PSD square root. This requires a proved PSD-complexification bridge and includes singular W and odd dimensions.
5. The actual upper Rayleigh bound for the real inverse and equality-to-eigenvector implication produce a real PSD top inverse eigenmatrix. Reciprocal ordering of positive eigenvalues, or an equivalent spectral proof, then gives the universal lower Rayleigh bound for the original Jordan operator. Finally `TKT=B⊗A` and `Tv=±v` give the factor-two identity in both sectors. The attained global PSD eigenmatrix lies in the symmetric sector; combining with attained skew minima yields the exact original comparison.

These bridges are explicitly listed by the dossier and absent as assumptions from the public types. Their implementation and actual consumption must be checked in final review. Approval here does not assert that they have already been proved.

## Exact numbers and independent diagnostics

The proposed LeanCert certificate is only `0<2`. It has a concrete required use: the full-n skew witness has squared Frobenius norm two, so this certificate establishes a positive denominator/nonzero witness and enables normalization for skew minimum attainment. Final review must reject an unused numerical decoration; no LeanCert execution or consumption is claimed at this stage.

My 177 independent diagnostics include every matrix unit through n=4 for vectorization, commutation and squared-norm conventions; transpose involution and tensor exchange; both sector signs; the skew norm through n=7 including excluded n=0,1; repeated-extremal examples; and the dossier's stated values. The illustrative symmetric and skew quotient values of four are correctly labelled as sampled values, not minima.

I additionally used the distinct noncommuting SPD pair `A=[[2,2],[2,5]]`, `B=[[7,2],[2,5]]`, with positive leading minors `(2,6)` and `(7,31)`. Exact rational inversion checks the Jordan inverse and transpose commutation. A genuinely complex Hermitian negative-eigenvector example gives the Sylvester contradiction value −6. Exact complex PSD positive/negative parts verify the full Frobenius cross-term identity, while an odd-dimensional singular extension checks the real-modulus square/norm identities. These checks detect convention/sign mistakes; they do not prove arbitrary-dimensional cone preservation or minima.

## Reuse, API, documentation and attribution

I independently inspected and type-checked the pinned Mathlib vectorization, positive-definite/PSD predicates, spectral positivity, Rayleigh extremum, square-root uniqueness and modulus APIs. Specialized real/complex matrix square-root and modulus applications type-check with the intended `MatrixOrder` and matrix operator-norm scopes; those scopes must remain separate from the actual Frobenius objective. The standard compact-sphere/minimum APIs and Euclidean inner-product instances are available. The dossier correctly identifies substantial remaining project bridges rather than presenting a list of generic API names as a proof.

The small definitions are appropriate problem-local wrappers around actual Mathlib objects. Names, module placement and the six-export decomposition are reviewable. The Comparator list covers every export and permits no definition holes; the pinned toolchain, LeanCert and Mathlib versions match the shared infrastructure. The complete original source and historical attribution remain preserved. George Stepaniants's requested full Caltech affiliation is present in the preparation README; no new contact email is added. Original Colbrook authorship and Kalantarova–Tunçel conjecture attribution are retained. AI assistance and independent AI-review status are disclosed. I make no new literature-completeness, priority, external-human-review or official Tau Ceti endorsement claim.

## Exact approved boundary hashes

| Project-relative input | SHA256 |
| --- | --- |
| `NLA/SP05/Definitions.lean` | `2dfb4549c6ad2fbab5b31d0fdac18510c49d68846cab79deabc794068188a5fb` |
| `Challenge.lean` | `df243901a25385eab79a8218526f788f8ded2516f607bad33dc0e9284b31b214` |
| `NUMERICAL_TARGETS.md` | `699affc08fc1c49e472ee45532666727f0bd92fe76d507db44da35b9d2f15cc1` |
| `comparator.json` | `7fbf962523d010b2ad65d7bbcdf7c1d1d8b563b3bcdf151f07757746dee36d64` |
| `lakefile.toml` | `fec57fbcbb1718db75a2606961d3c2531752b478ff97ea55efb1c0cb19405760` |
| `lake-manifest.json` | `a6d69cb5b925415edfbd2a68d86668713c13b703ae28154a3f67bdc30ababf9a` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `reviews/initial/independent-exact-check.py` | `ab688c7595ce49bc863fda9241484b038f1dcf9494abfa7b57e9a379db0ba9fa` |
| `reviews/initial/independent-exact-check.json` | `e78725b0b384e31e8a1a6732d47b203a3117392ef48293fcd9cc4cbe7f05d03c` |
| `reviews/initial/source-hashes.json` | `b69eb8f51dd41ceac1af86fd778b7bd861b46da11f4565b5a234ab0f66969243` |

Independent audit JSON SHA256: `dbb88bb82276226406fcb9e71ade001b216c0850d5b8406d0826640c7c82750c`.  
Evidence checksum-list SHA256: `9d7a25d3e00fe9d0dc8fa18541feb0b5214c9552576878c5b49bb3e1ab14540d`.

**Disposition:** no requested statement change. Approve these exact ten files for the pre-proof freeze. All six Challenge holes remain deliberate specifications; Solution still imports definitions only. Proof implementation, final independent source reviews, permitted-axiom closure, actual LeanCert kernel consumption, Comparator correspondence and reproducible Linux verification remain required before any Lean verified promotion.

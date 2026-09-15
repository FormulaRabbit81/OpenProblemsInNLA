# SP-05 independent complete-source review — referee 1

**Verdict: PASS for complete source, exact target correspondence and independently executed local kernel/axiom checks.** This approval is bound to candidate commit **`081423df8a2445285261bcef2edc8fd66945f200`** and the 23 exact inputs below. Actual isolated Linux verification, Lean4 Comparator and the two operational audits remain pending. Canonical status must remain **Solved** until those gates pass.

**Reviewer:** OpenAI GPT-6 Codex agent `/root/reference_api_review`, independent non-implementing AI referee. **Date:** 2026-09-15. I wrote no SP-05 mathematical implementation and changed only my review/evidence. I read all twelve NLA modules, all six Challenge signatures and proof wrappers, the complete original canonical/source proof and historical review, the frozen dossier, pins, README and metadata. This report covers fidelity, correctness, proof quality, reuse, generality, API, naming, placement, documentation and attribution under [the repository's Tau Ceti adaptation](../../../../docs/lean/REVIEW.md); it claims no official endorsement or external human peer review.

## 1. Exact original target and preservation

The original statement asks, for every n≥2 and arbitrary real symmetric positive-definite A,B, whether the least Rayleigh value of **A⊗B** on all nonzero vectors with Tv=v is at most the corresponding least value on all nonzero vectors with Tv=−v. It uses actual column vectorization and the commutation matrix. The source proves the stronger existence of a real nonzero PSD eigenmatrix at the global minimum of **A⊗B+B⊗A**, valid for n≥1.

The frozen definitions express those objects literally. `Matrix.vec` uses `(column,row)` indices, and its Kronecker identity is vec(BXAᵀ), with the correct factor order. `commutationMatrix` actually swaps those coordinates. `rayleigh` uses the real Euclidean dot-product quotient, and `sectorValues` ranges over every nonzero vector in the actual ±1 eigenspaces. `IsLeast` supplies both attainment and universal lower bounds; no empty-set infimum substitutes for a minimum. The stronger exported eigenmatrix is real, PSD and nonzero, has positive eigenvalue, and bounds the quotient of **every** nonzero real vector. Its eigen-equation yields attainment.

I matched all six public proof signatures literally against the independently approved Challenge, then independently elaborated those signatures against Solution. There is no commutativity, simple-spectrum, rational-entry, even-dimension or invertible-minimizer restriction. Singular minimizing matrices, zero eigenvalues of auxiliary PSD matrices and repeated extremal eigenvalues are covered. n=1 is correctly permitted for the stronger theorem; n≥2 guarantees the nonempty skew sector for the original statement.

All ten pre-proof inputs and both statement approvals remain unchanged from freeze commit `04d1de395494800390405f3df1645316fe7943c2`. All seven recorded original source files match published base `d8c38a795876b132c90df8d1be8682d3dcde394c`; canonical status is still Solved. The complete historical mathematical block has 3483 UTF-8 bytes and SHA-256 `54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42`. The permanent 217-ID registry is unchanged.

## 2. Full proof path independently inspected

**Basic identities and attained sectors.** `Basic` proves vectorization, transpose action and the Frobenius/dot-product bridge from actual Mathlib operations. The skew witness has exactly two nonzero entries in every n≥2, squared norm 2, and zero is excluded using the explicit LeanCert kernel certificate. `Sectors` normalizes any nonzero vector by its positive dot-product square root. Its unit sector is a closed subset of the finite coordinate box [−1,1]; compactness of that box is valid for the actual finite real product topology. The quadratic form is continuous, attains a minimum there, and quotient homogeneity transports that minimum to the full original sector. The identity vector and full-dimensional skew witness prove both sectors nonempty. This attainment lemma is correctly stronger than its public wrapper and does not require A,B positive definite.

`commutation_dot` and `commutation_kronecker` prove the permutation is orthogonal and interchanges tensor factors. The exact factor-two quotient identity is then established for both ε²=1 sectors. The final comparison uses the PSD minimizing eigenmatrix in the symmetric sector and the global lower bound against a vector attaining the skew minimum. It never replaces the original A⊗B quotient by the Jordan quotient without the factor-two bridge.

**Full complex cone and actual inverse.** `Complexification` constructs the actual entrywise map as a real star-algebra homomorphism. It proves PSD preservation using the scoped Loewner matrix order, PD preservation using units, inverse compatibility for units, and PSD-square-root naturality by uniqueness. These are genuine maps of coefficient matrices, not arbitrary positivity assumptions.

`Sylvester` proves that a Hermitian solution X of CX+XC≥0, with complex Hermitian C positive definite, is PSD: testing every actual eigenvector of X gives 2λ Re(v*Cv)≥0, and the second factor is strictly positive. Before applying this fact, the full complex Jordan operator is proved injective using a positive-definite Kronecker coefficient matrix. Equality of the equation with its conjugate transpose then proves its solution Hermitian. The B-square-root congruence uses both cancellation identities and explicit noncommutative multiplication; it does not assume A and B commute. Congruence back yields positivity of the full complex solution.

`Cone` connects this generic lemma to **the actual inverse of the actual Jordan coefficient matrix**. It proves complexification of Kronecker coefficients, the complex vectorization equation, inverse compatibility and the exact right-inverse equation on every complex matrix. Thus the PSD-preservation hypothesis of the modulus helper is discharged on the entire complex Hermitian cone, including iW in the skew branch; positivity only on real symmetric matrices is never substituted.

**Real modulus and true Frobenius comparison.** `Modulus` identifies its pairing with the real part of tr(X*Φ(Y)). The PSD trace-product sign is proved through a square-root congruence and trace cyclicity, without assuming its two factors commute. Writing a Hermitian matrix as P−N and its modulus as P+N yields two separately nonnegative cross terms. The proof uses 2 tr(PΦ(N))+2 tr(NΦ(P))≥0; equality of these terms is unnecessary. This is a valid simplification of the source's self-adjoint version, with a strictly more general helper and no weakened final target.

The real modulus equals the square root of WᵀW. Its complexification is the complex modulus by PSD-square-root uniqueness; multiplying by i changes neither modulus nor pairing. This proves the critical realness bridge for skew W, including singular W and odd dimension. The Frobenius-square identity is derived from trace and |W|²=WᵀW, **not** from a C*-operator-norm theorem. It proves nonzero modulus as well as equal vector norm. The resulting PSD real matrix has at least the original eigenmatrix's inverse quadratic quotient.

**Spectral minimum over all real vectors.** `Spectral` chooses a largest eigenvalue from the finite real spectrum of the positive-definite inverse and constructs the actual PSD slack rI−J⁻¹. `Jordan` uses transpose commutation to choose a nonzero symmetric or skew eigenmatrix; using W+Wᵀ without dividing by two is harmless because eigenvectors may be rescaled. The modulus inequality and PSD slack force the slack quadratic form to vanish; Mathlib's PSD kernel characterization proves the eigen-equation even when the extremal eigenvalue is repeated. A separate positive reciprocal-eigenvalue argument proves J−r⁻¹I PSD. `Minimizer` therefore produces the positive eigenvalue r⁻¹, a real nonzero PSD eigenmatrix, and the lower Rayleigh bound for every nonzero real vector. All helper hypotheses are supplied by earlier proved facts.

No mathematical gap, hidden target assumption or vacuous conclusion was found in this path.

## 3. Independent execution and numerical trust

I copied the exact project sources and pins into a separate fresh directory, with no project build cache, and reused only the pinned dependency cache. The source hashes of that compiled snapshot match the final committed candidate. Using Lean **4.33.1** (compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`):

- `lake build Challenge`: **exit 0, 2710 jobs**, exactly six intentional specification-only holes.
- `lake build Solution`: **exit 0, 3738 jobs**, no proof-hole warnings. The only two warnings concern retained unused positivity hypotheses in the stronger sector-attainment wrapper.
- Independent [`AuditFull.lean`](final-referee-1-evidence/AuditFull.lean): **exit 0**, six literal frozen public types, every one of the **81 project theorem declarations**, and two concrete nonvacuity instantiations (n=1 for the PSD minimum; n=2 for the original inequality). All **89 kernel-trust and transitive axiom checks** pass, using only `propext`, `Classical.choice` and `Quot.sound` or fewer axioms.
- Metadata schema and exact six-result Comparator coverage: **PASS**.
- All dependency Git revisions match the manifest and their tracked sources are clean.

`Certificates.skew_norm_positive_certificate` explicitly invokes `interval_decide (trust := kernel)` for 0<2. Its proof is consumed by `skew_frobenius_pos`, `skew_ne_zero`, `skew_sector_nonempty`, attained skew minimization and the canonical comparison. It is not decorative. No target or proof closure contains `sorryAx`, a custom axiom or a native decision axiom; source inspection also found no admissions, unsafe substitutions or Challenge imports in the proof implementation.

I independently reran and extended my own rational/Gaussian-rational diagnostic code: **183 exact checks pass**. They cover column ordering, tensor swapping and Frobenius products, the witness dimension boundary, a separate noncommuting SPD example and its true inverse, a complex negative-eigenvector sign test, complex PSD images, real singular/odd-dimensional moduli and repeated spectra. A new positive congruence-map sample has **unequal nonnegative cross terms 18 and 2**, with exact modulus gain 40; it directly checks the final two-cross-term simplification without assuming self-adjointness. These finite diagnostics supplement the universal Lean proofs and do not replace them.

## 4. Reuse, quality and truthful documentation

The implementation reuses the pinned Mathlib vectorization/Kronecker, Loewner-order, PSD/PD, finite Hermitian spectrum, functional-calculus square-root/modulus and compact-extremum APIs. I inspected the relevant installed source and the earlier pinned API/reuse assessment. The generic complex Sylvester and complexification helpers cover arbitrary finite index types; problem-specific definitions and wrappers remain in `NLA.SP05`. Names and module boundaries reflect the actual mathematics, and comments explain the cone, modulus and variational bridges. There is no unnecessary spectral approximation, expanded polynomial or integral computation. The coordinate-box compactness and integral-free cone proof reduce implementation work without narrowing the target.

The README and metadata accurately describe the complete local candidate, the two pre-proof approvals and the still-pending final/operational gates. The frozen preparation dossier retains its historical stage text rather than being retrospectively rewritten. Current documentation explicitly identifies both proof simplifications and the six deliberate Challenge placeholders. Pins, commands, licenses, reference reuse and contributor-versus-independent-review roles are disclosed. The requested formalization credit is George Stepaniants, **Department of Computing and Mathematical Sciences, California Institute of Technology**, without a new contact email. Original Colbrook/Cambridge authorship and Kalantarova–Tunçel conjecture attribution are preserved. Forsythe and Schiffer are credited as pinned structure/API references; no copied mathematical implementation or author endorsement is claimed.

## 5. Exact reviewed inputs

Every hash below matches both the working bytes I reviewed and its Git blob at `081423df8a2445285261bcef2edc8fd66945f200`. The [candidate seal](final-source-inputs.json) itself has SHA-256 `e2f04725624543606dbf1041a756385822944051ab9d1dac8557dbd35385c0e6`.

| Project-relative input | SHA-256 |
|---|---|
| `.gitignore` | `3b8ef443f22e1029ffe4683cc0b3950064f9559bba9b202d604e658bd3370bf6` |
| `Challenge.lean` | `df243901a25385eab79a8218526f788f8ded2516f607bad33dc0e9284b31b214` |
| `LICENSE` | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` |
| `NLA/SP05/Basic.lean` | `2083f47e17507e45d66920d8866cb61a2eee37000410ced4151f3eb66d6ae339` |
| `NLA/SP05/Certificates.lean` | `bc76925b25739cfc56f50c39a23abc48a927c91c4bb5e727edccc7996e9c66ef` |
| `NLA/SP05/Complexification.lean` | `e66e6fc9fb30d955ee536e24ad16d369302e7016495c2b8a11f7a03b95955ced` |
| `NLA/SP05/Cone.lean` | `2325a49743efb806591b938564f37979b40cc393427a7741b28dbc4820b84e5b` |
| `NLA/SP05/Definitions.lean` | `2dfb4549c6ad2fbab5b31d0fdac18510c49d68846cab79deabc794068188a5fb` |
| `NLA/SP05/Jordan.lean` | `80682d0d0164399ad34147860bcc1c605a93f6624778706188f2867def71c414` |
| `NLA/SP05/Minimizer.lean` | `66f011cd270ae3b6fbe61f5880eb6eb54e6f7f03dd91dd0d0c4f9400f2e9acaf` |
| `NLA/SP05/Modulus.lean` | `7b873ab8f1a9fe9987e518a0812f209f6a778dd05aca370a79a12934bdfc9cf1` |
| `NLA/SP05/Proof.lean` | `605c5f5e5a79aa9f8155a2b6f472045d1e8d089368752b873a595b6756d95449` |
| `NLA/SP05/Sectors.lean` | `fc0bf91a271e042568880666fbd285eb23452a06d888b58a6b70e2003899bdd5` |
| `NLA/SP05/Spectral.lean` | `6e9ca0b67b4dcee8cbb15c998f0e827b82703dcef3be41f2f76516a7061a7d8b` |
| `NLA/SP05/Sylvester.lean` | `88e4aff58b5eb2b564d7b27173de83548d768a22400e77bf296c8e1d06ae9c15` |
| `NUMERICAL_TARGETS.md` | `699affc08fc1c49e472ee45532666727f0bd92fe76d507db44da35b9d2f15cc1` |
| `README.md` | `89915860131b57f0a6a2cd93d63e64591ab1b40c28697f520b3fc08ce7ff19f2` |
| `Solution.lean` | `66753a1b36829f3edb9a4e23c4c7ebc37c5897c2fe94644ba5aea0ed0e6635b2` |
| `comparator.json` | `7fbf962523d010b2ad65d7bbcdf7c1d1d8b563b3bcdf151f07757746dee36d64` |
| `formalization.yaml` | `5f9a3d9b0b0fe99d429fe3974c359d4b66da9a4028497172456c9511646dfe2b` |
| `lake-manifest.json` | `a6d69cb5b925415edfbd2a68d86668713c13b703ae28154a3f67bdc30ababf9a` |
| `lakefile.toml` | `fec57fbcbb1718db75a2606961d3c2531752b478ff97ea55efb1c0cb19405760` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The independent [audit JSON](final-referee-1-evidence/audit.json) records **248 passing source/pin/signature/closure checks**, all ten frozen hashes, all original source hashes, the actual compiler/dependencies and all 89 theorem closures. [Sealed evidence](final-referee-1-evidence/SHA256SUMS) includes my executable audit, fresh build logs, exact-type/trust audit and independent arithmetic. My own execution results, not contributor PASS messages, support this verdict.

**Final source disposition: PASS.** No proof changes requested. This is not a successful Comparator run or an authoritative Linux verification claim. Those must be executed on the reviewed source, independently audited, and followed by a truthful publication review before status promotion. No new literature-completeness search, novelty certification, external human review or official Tau Ceti endorsement is claimed.

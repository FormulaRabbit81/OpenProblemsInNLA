# SP-05 — independent final full-source referee 2

**Verdict: PASS for the complete source candidate.** No substantive mathematical, scope, proof-trust, or attribution defect was found. This approves the exact candidate below for the next verification stage; it does **not** approve promotion to Lean verified. Actual isolated Linux Comparator/default-kernel execution and independent operational audits remain pending.

**Reviewer:** OpenAI Codex AI agent `/root/existing_verification_audit`, 15 September 2026. I did not implement or edit any SP-05 definition, theorem, proof, or candidate document. This is an independent AI-agent review under [the repository's Tau Ceti adaptation](../../../../docs/lean/REVIEW.md), not human peer review or an official Tau Ceti endorsement. I independently inspected every source module, complete canonical target and original proof, built a fresh project snapshot, and ran the checks described below. Author/contributor build claims were not used as substitutes for my checks.

## Exact reviewed identity

- Complete candidate: **`081423df8a2445285261bcef2edc8fd66945f200`**.
- Published input base: `d8c38a795876b132c90df8d1be8682d3dcde394c`.
- Pre-proof freeze: `04d1de395494800390405f3df1645316fe7943c2`.
- [Final 23-input manifest](final-source-inputs.json) SHA-256: **`e2f04725624543606dbf1041a756385822944051ab9d1dac8557dbd35385c0e6`**.
- [My complete evidence receipt](final-referee-2-evidence/review-evidence.json) SHA-256: **`aea3541d5c6f18c71630fbd6d75010ff4dd9c1fe617316f25a787693a8abc6c4`**. It includes every actual candidate-input hash and the independent snapshot hashes, not just the manifest's claims.

I independently matched all **23** manifest inputs to both current bytes and the exact candidate's Git blobs; all **10** pre-proof inputs to current bytes and the freeze's Git blobs; and all **17** build-snapshot source/configuration files to the candidate. Both sealed pre-proof referee reports remain unchanged, including my earlier report hash `7c20df0a8af3245e0c04219c0631fe7b020a8760fcf60588a01c64acf285149f`. The original seven canonical/source files and historically reviewed 3483-byte mathematical block remain byte-identical to their pinned input base. The permanent SP-05 registry path is unchanged.

Notable exact hashes are:

| Input | SHA-256 |
|---|---|
| `NLA/SP05/Definitions.lean` | `2dfb4549c6ad2fbab5b31d0fdac18510c49d68846cab79deabc794068188a5fb` |
| `Challenge.lean` | `df243901a25385eab79a8218526f788f8ded2516f607bad33dc0e9284b31b214` |
| `NLA/SP05/Proof.lean` | `605c5f5e5a79aa9f8155a2b6f472045d1e8d089368752b873a595b6756d95449` |
| `Solution.lean` | `66753a1b36829f3edb9a4e23c4c7ebc37c5897c2fe94644ba5aea0ed0e6635b2` |
| `README.md` | `89915860131b57f0a6a2cd93d63e64591ab1b40c28697f520b3fc08ce7ff19f2` |
| `formalization.yaml` | `5f9a3d9b0b0fe99d429fe3974c359d4b66da9a4028497172456c9511646dfe2b` |

## Complete-target fidelity

The canonical target quantifies over every `n ≥ 2` and all real symmetric positive definite A,B. Its two minimum expressions range over **all nonzero real vectors** in the +1 and −1 eigenspaces of the literal commutation matrix. `sectorValues` contains exactly those quotients; `IsLeast` includes an actual realizing vector and its comparison with every admissible vector. No infimum of an empty set or unattained lower bound is substituted.

The stronger `positive_minimizer` theorem includes every `n ≥ 1`, a positive real eigenvalue μ, a real nonzero PSD eigenmatrix, and a lower Rayleigh bound against every nonzero real vector. The eigen-equation and strictly positive squared denominator prove attainment. Nothing assumes A and B commute, simple eigenvalues, even dimension, rational entries, an invertible minimizing matrix, cone preservation, or pre-existing minima.

`Matrix.vec` literally uses (column,row) indices and is bijective. `kronecker_columnVec` invokes the actual Mathlib convention to give `vec(B X Aᵀ)`. The sum therefore represents `AXB+BXA` for symmetric A,B. The commutation matrix is the actual index-swap permutation. `columnVec_dot_self`, trace-pairing identities and `real_abs_vec_norm_sq` establish the genuine Euclidean/Frobenius square; no default Pi norm or C*-operator norm is used in place of that square. `dot_self_pos` excludes zero denominators in every quotient argument.

I separately loaded Challenge and Solution into Lean with explicit pretty-printing. All six elaborated exported types are **byte-identical**. Source wrappers also retain the literal frozen signatures. This local elaboration comparison is not a claim that Lean4 Comparator has run.

## Actual proof audit

### Full complex inverse cone — PASS

`Complexification.lean` defines the entrywise real-to-complex map as a genuine real star-algebra homomorphism and proves PSD/PD preservation. Its inverse identity requires an actual unit; its square-root identity uses PSD uniqueness and therefore includes singular inputs. The scoped matrix order is explicitly the Loewner order, whose nonnegativity is equivalent to `Matrix.PosSemidef`, not entrywise order.

`complex_jordan_injective` proves injectivity on the **full complex matrix space** using the positive definite Kronecker coefficient matrix. Transpose positive definiteness is the appropriate complex Mathlib theorem; no transpose is mistaken for conjugate transpose. `complex_jordan_preimage_hermitian` uses uniqueness and the actual adjoint equation, so Hermitian symmetry of the solution is proved rather than assumed.

The Sylvester argument then checks every eigenvector of Hermitian X. The exact complex quadratic identity has real scalar `2*ev`; C's strict positivity and the nonzero orthonormal eigenvector force `ev ≥ 0`. For the congruence reduction, all U/V square-root and inverse cancellations are supplied before defining `C=V*A*V` and `S=U*X*U`. The forward and inverse congruences preserve the noncommuting multiplication order. `Cone.lean` identifies the actual complexified inverse coefficient action with the actual Jordan equation, so its cone theorem covers every complex Hermitian PSD right-hand side. No unproved existence, reality, or integral bridge remains.

This integral-free proof establishes precisely the inverse positivity property used by the original complete source. It adds no hypothesis and eliminates unnecessary exponential integration.

### Modulus, realness and Frobenius square — PASS

`complexPairing_trace` is the real part of the genuine complex Frobenius pairing. The trace of a product of two PSD matrices is shown nonnegative by square-root congruence and trace cyclicity, without assuming the product itself is PSD. In `hermitian_modulus_pairing_le`, both cross terms are individually nonnegative. Keeping their sum instead of combining them by self-adjointness is valid and slightly more general than the source helper.

The symmetric and skew cases are both handled. In the skew case `i*W` is genuinely complex Hermitian. `complexify_abs_I_smul` identifies its modulus with the complexification of the real PSD `CFC.abs W`, using square-root naturality on `WᵀW`. No inverse of W appears, so singular skew matrices, odd dimensions, and zero eigenvalues are included.

`real_abs_vec_norm_sq` proves equality of **Frobenius squared norms** by exact trace/vectorization and `|W|²=WᵀW`; it does not misuse the C*-norm absolute-value theorem. Nonzero modulus follows from positive vector squared norm. The improved inverse quadratic form is therefore on a real nonzero PSD matrix with the same actual denominator.

### Spectral extremum and every-vector minimum — PASS

`real_spectral_max` chooses an actual member of the finite nonempty eigenvalue family, proves positivity, and constructs the PSD slack `rI-P`. The symmetric-or-skew extraction is exhaustive: if `W+Wᵀ` vanishes, W itself is skew; otherwise the nonzero sum is symmetric. Inverse commutation is proved using injectivity of the original positive definite operator.

`psd_slack_eigenvector` invokes the genuine PSD quadratic-zero/kernel equivalence, so equality at a repeated extremum still implies an eigenvector equation. `inverse_slack_lower` proves the reciprocal bound on each actual positive eigenvalue of J and transfers it to Loewner order. The final real quotient lower bound uses its positive dot-product denominator. Thus `global_positive_minimizer` is a global all-vector result, not only a bound on symmetric vectors.

### Attained full sectors and exact original comparison — PASS

`unitSector_isCompact` proves that the literal dot-product unit sector is a closed subset of the coordinate box `[-1,1]`; each coordinate bound follows from its square being a term in the sum. This topology argument needs no equality with the default Pi norm. `normalize_sector` uses the positive square root of the actual dot product, preserves the linear sector equation, and proves quotient homogeneity. Compactness and continuity therefore yield `IsLeast` for the full nonzero-vector quotient set.

The identity matrix supplies the symmetric witness for every n≥1. `E₀₁-E₁₀` supplies the skew witness for every n≥2. Both dimensions and the nonzero requirement are proved. The literal commutation identity yields the factor two for both signs. The PSD global eigenmatrix supplies a symmetric value μ/2; the global lower bound applies to the actual attained skew witness. The resulting `a ≤ b` is the canonical statement without extra assumptions. The stronger sector-attainment helper is valid for arbitrary A,B; the public wrapper keeps the exact positive-definite hypotheses.

## LeanCert consumption, reproducibility and trust

The only numerical interval proof is the exact `(0 : ℝ) < 2`, using **`interval_decide (trust := kernel)`**. It feeds `skew_frobenius_pos`, then `skew_ne_zero`, nonempty skew sector, normalization and minimum attainment. I additionally traversed actual compiled declaration expressions with [DependencyAudit.lean](final-referee-2-evidence/DependencyAudit.lean): the certificate is reachable from `skew_witness`, `sector_minima`, and `canonical_result`, visiting respectively 15, 38 and 97 project constants. This confirms genuine theorem dependency, not just import or textual proximity. [Actual output](final-referee-2-evidence/certificate-dependency.log).

My fresh source snapshot at `/private/tmp/nla-campaign-existing-review/SP05-final-build` had its own project build directory. Only the pinned dependency packages were reused. `lake build Challenge Solution` independently succeeded with **3740 jobs**. The only proof-hole warnings are the six deliberately frozen Challenge placeholders; Solution does not import Challenge. The two unused `hA`/`hB` warnings are harmless consequences of stronger sector attainment and preserve the exact reviewed wrapper type. [Build log](final-referee-2-evidence/fresh-build.log).

The independent [FinalAudit.lean](final-referee-2-evidence/FinalAudit.lean) checks all **81** named theorem closures with `#assert_trust kernel` and `#print axioms`, including the six exports and all project helper theorems. Every closure passed and uses only `propext`, `Classical.choice` and `Quot.sound`. [Audit log](final-referee-2-evidence/independent-trust-axioms-types.log). No project axiom, `sorry`, admission or native-execution proof exists in the actual Solution import closure.

I verified Lean 4.33.1's actual binary version and all ten resolved package revisions against the manifest, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. [Pins](final-referee-2-evidence/toolchain-and-package-pins.json). The [schema/Comparator coverage validator](final-referee-2-evidence/manifest-validation.log) independently passed for all six results.

My independently written exact pre-proof diagnostics were rerun for this phase: all original source hashes, noncommuting vectorization conventions, complex Sylvester sign identity and singular odd-dimensional skew modulus checks passed. The first attempted rerun stopped at the script's intentionally obsolete assertion that Solution still contained no proofs; the retained phase note and copied script document changing only the expected Solution import/module count and output label. No mathematical diagnostic or previous evidence was weakened or edited. These finite checks corroborate conventions; the universal proofs are the compiled Lean theorems.

## Reuse, documentation and attribution

I inspected the used pinned Mathlib PSD order/spectral facts, Kronecker/vectorization API, PSD quadratic-zero theorem, and CFC modulus/square-root theorems. The implementation appropriately reuses these rather than introducing custom axioms or an alternative matrix-positivity model. Generic finite-index Sylvester and complexification helpers are separated from the problem-specific sector/operator definitions; names and comments make the proof route inspectable. No substantive API or maintainability change is required for this candidate.

README and schema-valid metadata accurately describe a complete locally built candidate with final reviews and real Linux verification still pending. Frozen preparation-stage labels in Definitions and the dossier are retained historical boundary text, not updated proof-status claims; the current README explains the completed implementation and the six intentional specification holes. Metadata records zero **proof-development** holes with that distinction explicit. It makes no unrun Comparator/default-kernel claim.

George Stepaniants receives the requested Department of Computing and Mathematical Sciences, California Institute of Technology affiliation; no contact email was added. Matthew J. Colbrook retains the original mathematical proof credit and Cambridge affiliation, and Kalantarova–Tunçel retain conjecture credit. Preserving the original source's existing author metadata is distinct from adding a formalizer contact address. AI assistance, independent-agent review and the absence of external human review/author endorsement are disclosed. The original canonical page, problem ID and source proof remain unchanged.

## Remaining gate

**PASS is limited to these exact source bytes and local evidence.** I did not run the isolated Linux harness or Lean4 Comparator in this review. The candidate must still pass the actual default-kernel Comparator, authenticated source receipt, real sandbox and rejection controls, followed by independent operational review. Keep canonical status **Solved** until those gates pass. All review evidence is sealed by [SHA256SUMS](final-referee-2-evidence/SHA256SUMS).

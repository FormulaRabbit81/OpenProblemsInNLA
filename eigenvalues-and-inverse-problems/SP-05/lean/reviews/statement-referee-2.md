# SP-05 independent statement referee 2

**Verdict: APPROVE the exact pre-proof mathematical and numerical boundary identified below.** I found no target weakening, extra mathematical hypothesis, vacuous minimum, or unresolved statement defect. This is permission to implement these reviewed targets under the repository review process; it is not proof acceptance or a Lean-verification claim.

**Reviewer:** OpenAI Codex agent `/root/existing_verification_audit`, an independent AI reviewer and non-implementer. **Date:** 2026-09-15. I changed only this review and its evidence. I applied `docs/lean/REVIEW.md`'s Tau Ceti adaptation, covering fidelity, mathematical correctness of the proposed route, reuse/API, documentation, and attribution. This is neither external human peer review nor an official Tau Ceti service result.

## Frozen inputs and canonical preservation

The input manifest is `reviews/statement-inputs.json`, SHA-256 **`69efa93665a3cbaaf26037402329e8d9f7aa552358e5e300dbfaf27af71e0e89`**. I recomputed all ten hashes before and after my checks. Approval is specific to these bytes, not an anticipated implementation:

| Input | SHA-256 |
|---|---|
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

I read the complete canonical statement, original mathematical proof in `solution.md` and its LaTeX rendering, historical independent review, all definitions, all six signatures, the entire dossier, diagnostic source/output, and API probe. I independently confirmed every one of the seven recorded canonical/source file hashes against both current bytes and Git base **`d8c38a795876b132c90df8d1be8682d3dcde394c`**. The permanent registry still maps SP-05 to its original canonical README. The unchanged historical mathematical block has 3483 bytes and SHA-256 **`54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42`** under its stated normalization. The exact source hashes are also retained in my independent evidence JSON.

I independently opened the [primary arXiv v3 manuscript](https://arxiv.org/pdf/1805.09737v3): printed page 12, Conjecture 1, equation (7) is the positive-definite minimum-sector comparison; printed page 2 fixes the column-vectorization convention. The dossier and canonical target agree with those locators. Earlier interlacing results for general symmetric matrices and maximum-eigenvalue questions are not substituted for this target.

## Exact target correspondence

The original target quantifies every dimension n≥2 and every pair of real symmetric positive-definite n×n matrices A,B. It compares attained minima of the actual A⊗B Rayleigh quotient over all nonzero vectors in the transpose permutation's +1 and −1 eigenspaces. The source's stronger conclusion is an actual real nonzero PSD eigenmatrix attaining the global minimum of A⊗B+B⊗A.

- `Matrix.vec X (column,row) = X row column` is the imported definition. Thus `A⊗B` acts as `X ↦ B X Aᵀ`; the first `column_vectorization` conjunct has exactly the right factor order for arbitrary, even nonsymmetric, matrices. The permutation matrix's literal entries implement index swap, and the norm bridge is the ordinary sum of squares of every entry. The product index has n² coordinates.
- Imported `Matrix.PosDef` and `Matrix.PosSemidef` include Hermitian symmetry. On real matrices this is transpose symmetry. Their finite-support quadratic forms quantify all vectors in the finite index space. These are spectral PSD/PD conditions, not entrywise positivity.
- `sectorValues` includes every nonzero real vector satisfying the actual permutation equation. Its denominator is the literal Euclidean square `dotProduct v v`; nonzero real vectors give a positive denominator. No default function norm, matrix operator norm, finite sample, or stationarity condition replaces it.
- `IsLeast S a` asserts both membership and universal minimality. The membership gives an actual nonzero attaining vector. Therefore `sector_minima` and `canonical_result` cannot succeed using an empty-set infimum or an unattained lower bound.
- `positive_minimizer` gives μ>0, a real PSD nonzero X, the actual Jordan eigen-equation, and a lower bound for **all** nonzero real vectors. Injectivity of `Matrix.vec` and the eigen-equation force X's Rayleigh value to be μ, so attainment is part of the mathematical content even without an additional redundant `IsLeast` predicate.
- The stronger assertion requires n≥1. The canonical inequality and both-sector existence require n≥2. The explicit skew matrix has precisely two nonzero entries, squared Frobenius norm 2, and works in all n≥2, including odd dimensions. Singular minimizing matrices and repeated eigenvalues remain allowed. The n=0 nonzero-eigenmatrix impossibility is excluded.

The six Comparator names exactly cover `numerical_bound`, `column_vectorization`, `skew_witness`, `positive_minimizer`, `sector_minima`, and `canonical_result` in namespace `NLA.SP05`. Each actual signature matches dossier §8. The first certificate is exactly `(0 : ℝ) < 2`; it must be consumed through the arbitrary-dimension skew witness's positive square norm and normalization. There are no definition holes, and only the three standard permitted axioms are configured. Neither an inverse-positivity assumption nor a preexisting minimizer is hidden in any signature.

## Mathematical route: independent assessment

**The proposed integral-free replacement is sound and preserves the full source result.** For Hermitian PSD Y, first use the positive-definite complexified Jordan operator to obtain the unique X solving L(X)=Y. Adjoint commutation and uniqueness give X*=X. Congruence by B's positive square root reduces to `C X̃ + X̃ C = Ỹ`, with C Hermitian PD and Ỹ PSD. This reduction uses exact adjacent inverse cancellations and does not commute A with B.

If X̃ had a negative real eigenvalue λ with nonzero complex eigenvector v, Hermitian symmetry gives both `X̃v=λv` and `v*X̃=λv*`. Consequently

`Re(v*Ỹv) = 2λ Re(v*Cv) < 0`,

contradicting Ỹ's PSD property. The argument applies to the full complex Hermitian cone. It does not infer complex positivity from real positivity. Congruence back gives X PSD. The dossier correctly leaves existence, uniqueness, Hermitian symmetry, complexification, and all square-root cancellations as proof obligations. The integral formula itself need not be formalized when the exact property used downstream is proved this way.

I also checked the rest of the source argument independently:

1. The real inverse is self-adjoint PD and commutes with transpose. Its top real eigenmatrix has a nonzero symmetric or skew part, even for repeated extremal eigenvalues. Complex linearity makes H=W or H=iW a nonzero Hermitian eigenmatrix.
2. Positive and negative parts P,N satisfy H=P−N and |H|=P+N. Self-adjointness and the real trace symmetry on Hermitian matrices make the two cross terms equal. Complex PSD preservation gives `4 tr(P Φ(N)) ≥ 0` without requiring P and Φ(N) to commute. Cyclicity and PSD square-root congruence justify the sign.
3. The Frobenius square equality follows from `|H|²=H²` and trace, or the orthogonal spectral parts. A C*-algebra operator-norm identity alone would not be sufficient; the dossier explicitly distinguishes it.
4. In the skew case `H²=-W²=WᵀW` is real PSD. The real PSD square root becomes a complex PSD square root after a proved complexification bridge; uniqueness identifies it with |H|. It is real and nonzero even when W is singular or n is odd. The analogous symmetric case is included. These statements are obligatory proof bridges, not added premises.
5. The modulus has real inverse Rayleigh quotient at least the top eigenvalue and no greater than it. Equality implies its eigen-equation without simplicity. Positivity and reciprocal spectral ordering give the smallest Jordan eigenvalue and its universal lower bound.
6. The literal transpose permutation identities yield the factor-two quadratic-form identity on each sector. Both Euclidean unit-sector spheres are compact and nonempty, and normalization transfers their minima to all nonzero vectors. The symmetric PSD global minimizer then yields exactly the original inequality for A⊗B, not only the Jordan sum.

No mathematical gap or target reduction was found in this plan. Approval of the plan does not imply these steps have been implemented.

## Own mechanical and arithmetic checks

I created a fresh source snapshot at `/private/tmp/nla-campaign-existing-review/SP05-statement-build`, with no project `.lake/build`. It contains the ten exact boundary files and the definitions-only Solution. Only the pinned dependency package/cache directory is shared. Lean reports **4.33.1**; actual Mathlib and LeanCert Git revisions match the manifest.

With the pinned binary directory prepended to PATH, I ran:

```sh
lake build Challenge
lake env lean reviews/initial/ApiProbe.lean
lake env lean StatementAudit.lean
python3 reviews/statement-referee-2-evidence/independent-audit.py /private/tmp/nla-formalization-sp05-20260915
```

The fresh project build succeeded (2710 jobs) with **exactly six intentional Challenge `sorry` warnings**. The API probe succeeded independently. `StatementAudit.lean` contains imports, `#check`, and `#print axioms` only; it exposes the six actual types and their intentional `sorryAx` placeholder dependency. Those placeholders establish no mathematics and are not approved for any final proof. There are no project proof modules: the only current NLA file is Definitions, and Solution imports it only.

My independently written `independent-audit.py`:

- recomputes all ten frozen hashes and seven source hashes, checks source bytes against the published base, preserves the ID, and recomputes the historical proof-block hash;
- reruns the contributor's retained diagnostic and reproduces its JSON byte for byte;
- independently reconstructs the supplied noncommuting n=2 SPD example, K, J, principal minors, sampled values 4, and Sylvester sign example −4;
- independently checks general nonsymmetric column/Kronecker conventions, TKT, Frobenius squares, skew witnesses and sector factor-two identities in dimensions 1 through 6 where applicable;
- uses exact Gaussian rational arithmetic for a genuinely complex noncommuting Hermitian example with λ=−1, `v*Cv=3`, and `v*Yv=−6`, verifying the identity behind the inverse-positivity contradiction;
- checks a singular odd-dimensional real skew matrix, its Hermitian iW and real PSD modulus, equal Frobenius squares 8, and the positive/negative-part algebra.

These are finite diagnostics, never substitutes for the universal theorem. In particular, the value 4 in the supplied example is not claimed to be either sector minimum. All checks passed. The full commands, outputs, scripts and hashes are sealed under [statement-referee-2-evidence](statement-referee-2-evidence/).

## Reuse, attribution and remaining gates

The draft uses the actual imported Kronecker, vectorization, PSD, spectral, CFC and Euclidean APIs. I inspected the central definitions and relevant theorem types, and reran the probe. The remaining project lemmas are real obligations; the dossier does not mislabel an available API name as an implemented proof. Its explicit matrix-order and Frobenius warnings address meaningful instance risks.

The original mathematical proof remains attributed to Matthew J. Colbrook with its historical disclosures. The new package credits George Stepaniants and the requested Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, without adding a contact email. Original source metadata is preserved. The README and dossier accurately describe preparation, independent AI review, and the canonical Solved status; no premature verified metadata is present.

**No changes requested for this boundary.** Later approval still requires actual complete proof-source review, genuine consumption of the explicit LeanCert kernel certificate, exact Comparator correspondence, permitted-axiom checks on all implemented proof closures, and successful reproducible isolated Linux verification. None of those later results is claimed here.

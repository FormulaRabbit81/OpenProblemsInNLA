# IE-17 certificate modules — independent interim review

**Interim verdict: PASS for the reviewed `NumericData.lean` and `Certificates.lean` bytes. No target weakening or certificate discrepancy found. This is not full-target approval.**

Reviewer: OpenAI GPT-6 Codex `/root/reference_api_review` (independent AI), 2026-09-15. I authored neither module nor any IE-17 Lean proof. I read their actual complete source, the frozen Definitions, the prior numerical dossier/check evidence, the relevant pinned Euclidean-space APIs, and the use sites in the current `Optimal.lean`. I made no project/source edits.

## Exact reviewed source and environment

- `NLA/IE17/NumericData.lean`: SHA256 `3b325395a1ef8fa168261e4e0d3d146817bb1168778b8be4877f672c21fed495`.
- `NLA/IE17/Certificates.lean`: SHA256 `fa804a3211cbe1c000e981f13ab6823e139a7c04c503c6a1e77f98e78b40f5b9`.
- Frozen `Definitions.lean`: SHA256 `5b151dd47f4ea35ac2ca0e51900b588ccac214ed9660704e98757cfb7cbe9344`, unchanged from pre-proof freeze `5d9ae3c93298fc45f7d67341f6926b95e0f0be44`.
- Consumer read for usage only, `Optimal.lean`: SHA256 `dcae97798779d480c606b504c7ac949bfd43d5f644927c29864bd0d93a987ae1`.
- Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Complete copied input hashes are in `/private/tmp/nla-ie17-certificates-referee1/inputs.json`.

I rehashed these copied source/config inputs against the authoritative project after completing the independent checks; they remained equal. Challenge, manifest, toolchain, Lakefile and Comparator configuration retain their approved hashes.

## Actual independent compilation and axiom inspection

I copied the reviewed modules and necessary source/config files into `/private/tmp/nla-ie17-certificates-referee1/project`, using a fresh project build directory and only a symlink to the pinned dependency packages. No source-project `.olean` outputs were copied.

- `lake build NLA.IE17.Certificates` with the exact pinned compiler passed at **3631 jobs**, freshly compiling Definitions, NumericData and Certificates without warnings.
- My independent `Audit.lean` imports Certificates and invokes `#check`, `#print axioms`, and `#assert_trust kernel` on **18 declarations**: all 11 public NumericData lemmas and all seven public Certificate definitions/theorems. `lake env lean Audit.lean` exited 0.
- Every printed transitive axiom list is exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, native-decision axiom, or project assumption occurs. Private signed-square lemmas are covered transitively by the public certificate closures. Source inspection found no proof placeholder or native-decide invocation in the two modules.

Raw evidence and the audit source are retained under `/private/tmp/nla-ie17-certificates-referee1/`; `result.json` records commands, exits, source hashes, all closure lists and evidence hashes. This is a fresh local module build and trust audit, not a claim of a second Linux run or Comparator acceptance.

## Mathematical review

**Euclidean semantics and numeric data.** The norm-square lemmas directly use Mathlib's `EuclideanSpace.real_norm_sq_eq`; their finite coordinate sums equal actual L2 norms. The coordinate application lemma is the definitional matrix linear-map application on `Vec n = EuclideanSpace ℝ (Fin n)`. I inspected pinned `Matrix.toLpLin`/`toEuclideanLin` and their apply lemmas. No plain function-space or matrix default norm is substituted. All three iterate norms, three residual vectors and the two active residual norms equal the values independently reconstructed during my 42-check pre-proof Fraction audit.

**Feasible upper perturbation.** `witnessE` has all 12 entries and the common denominator from the frozen rational completion. `witnessE_feasible` proves the actual unchanged `Feasible` normal equations with b fixed; it does not assume feasibility or constrain the eventual error set to this rational witness.

**Upper signed-square identity.** `upperSOS` contains precisely the three reviewed positive diagonal margins and the three absolute off-diagonal coefficients of M, with signs `(a+b)`, `(a−c)`, `(b+c)`. The arguments `(y₀+18y₁−23y₂,y₁,y₂)` are exactly T⁻¹y for the frozen T. The proof establishes the full equality

`dM * ((1979/2000)‖y‖² − ‖Ey‖²) = upperSOS(T⁻¹y)`

for **every real Euclidean y**, using exact arithmetic and `ring`. Nonnegativity of each square and the positive exact dM imply the exported every-vector bound. The proof keeps the actual matrix map and L2 norms in the target; it does not use an entrywise or Frobenius bound. Proving nonnegativity rather than the stronger positive definiteness is sufficient for the frozen non-strict upper bound and does not weaken that target.

**Lower signed-square identity.** All four diagonal coefficients are exactly vᵢ times the frozen weighted margins for `v=(10000,10,185,1287)`. The six off-diagonal coefficients are `|Kᵢⱼ|vᵢvⱼ`, with the reviewed three negative and three positive signs. Substitution of `(u₀/10000,u₁/10,u₂/185,u₃/1287)` correctly reverses that diagonal congruence. The actual proved identity is

`dK * (lowerQuadratic u − (9901/10000)‖u‖²) = lowerSOS(diag(v)⁻¹u)`.

`lowerQuadratic` expands the genuine `(5/6)C+(1/6)D₂` quadratic form using the unchanged residual, actual `Aᵀu`, and the exact positive squared x₂ norm. The exported bound is universal over every real `u : Vec 4`; it adds no positivity, rationality or unit-direction restriction. The exact `9901/10000` margin remains stronger than the original strict `99/100` requirement. `zero_new_residual_certificate` separately proves the bound needed when a feasible perturbation makes the new residual zero, retaining that essential branch.

**LeanCert use.** `certificate_cutoffs` proves three exact rational comparisons with `interval_decide (trust := kernel)` for each goal. Its source has an explicit `#assert_trust kernel`, and my own independent trust check and printed closure agree. This is an actual LeanCert kernel proof rather than a comment declaring a mode. I inspected current `Optimal.lean`: it consumes `certificate_cutoffs.1.le` in the operator-norm bridge and `certificate_cutoffs.2.2` in the strict lower comparison. The certificates also feed the actual all-feasible-perturbation bound there. I have not independently compiled or approved that entire consumer/dependency chain in this bounded interim audit.

## Quality, reuse and attribution

The proof replaces the reviewed matrix congruences with explicit, kernel-checked signed-square identities; no eigenvalue search or larger optimization computation is introduced. Private certificate polynomials avoid an unnecessary public alternate matrix API. The NumericData helpers reuse Mathlib's genuine Euclidean norm formula and serve the concrete arithmetic and downstream modules. The dimension-specific expansions have actual consumers; no material proof duplication or invented norm implementation was found. The original Matthew J. Colbrook counterexample attribution and George Stepaniants/Caltech formalization credit are present, and the new auxiliary certificates are explicitly linked to their pre-proof dossier review.

**Remaining before full approval:** inspect and independently verify the completed LSMR run, all-perturbation norm/attainment reasoning, Moore–Penrose/projector bridge and uniqueness, all eight final exports, and the final artifact/metadata. Then run full permitted-axiom and real Linux Comparator verification against the frozen Challenge. This interim PASS cannot justify a Lean-verified status promotion on its own.

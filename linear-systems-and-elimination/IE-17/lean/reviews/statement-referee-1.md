# IE-17 independent pre-proof statement referee 1

**Verdict: APPROVE the exact statement boundary and numerical dossier at the hashes below.** I found no domain restriction, norm substitution, omitted minimum attainment, arbitrary-iterate substitution, pseudoinverse substitution, vacuity, or loss of either original monotonicity claim. The new upper congruence and lower weighted-dominance certificates pass my independently authored exact-arithmetic checks and preserve the original target.

Reviewer: OpenAI GPT-6 Codex agent `/root/reference_api_review` (AI), 2026-09-15. I did not author the boundary, dossier, or its initial arithmetic checker and have implemented no IE-17 Lean proof. This is independent AI statement/numerical review using the Tau Ceti correctness, scope, generality, reuse and attribution standards; it is not external human peer review or official Tau Ceti endorsement.

This is a **pre-proof approval**, not a formal verification. The eight Challenge placeholders are intentional specifications and prove no mathematics. No Solution proof, Comparator acceptance, target axiom clearance, or authoritative Linux result is claimed for IE-17 by this report.

## Materials and independent checks

I read the complete canonical README, complete original manuscript, all actual imported project definitions, all eight Challenge signatures, Comparator configuration, pinned environment files, and the final repository [NUMERICAL_TARGETS.md](../NUMERICAL_TARGETS.md), including its final §8 alignment and new §§4.1/5.1 certificates. I read the supplied initial checker and records after developing my own arithmetic reconstruction; my check does not import or invoke that checker.

I copied the six Lean/configuration inputs into an independent fresh local project directory, linked only the pinned dependency packages, and ran `lake build Challenge` with Lean 4.33.1. It succeeded at 2379 jobs, freshly compiling Definitions and Challenge, with exactly the eight expected specification-hole warnings. Its [raw log](statement-referee-1-evidence/statement-build.log) is retained. I rechecked that these copied input bytes equal the final authoritative project bytes. This confirms elaboration and types, not theorem truth.

My separately authored standard-library `fractions.Fraction` [arithmetic checker](statement-referee-1-evidence/independent_arithmetic.py) passed **42 exact checks**, retained in [its output](statement-referee-1-evidence/independent_arithmetic.json). It derives the Krylov normal equations and solves them from the integer A,b, reconstructs the feasible E from the manuscript formula, and calculates all certificate matrices itself. It does not accept a generated `PASS` as evidence or use floating-point optimization. Reproduce with `python3 reviews/statement-referee-1-evidence/independent_arithmetic.py` from the project directory.

## Semantic fidelity: actual definitions

- **Euclidean norms:** `Vec n` is `EuclideanSpace ℝ (Fin n)`. `spectralNorm` is explicitly the operator norm of `A.toEuclideanLin.toContinuousLinearMap`. The pinned `toEuclideanLin` acts between L2 spaces also for rectangular matrices. No default matrix norm, function-space supremum norm, or Frobenius norm enters this definition. `spectralNorm_semantics` requires the correct universal-vector characterization for every real rectangular E and nonnegative bound c, including empty/zero-dimensional edge cases.
- **Matrix-only attained minimum:** `Feasible` is exactly the original perturbed normal equation with its sign reversed, hence the same zero set; b remains fixed. `errorSet` includes every real m-by-n E, without rank, support, symmetry or rationality restriction. `IsOptimalError = IsLeast errorSet` includes membership/attainment as well as comparison with every feasible norm; it cannot hold by an empty-set convention. `optimal_errors` demands actual minima at both compared iterates. A global total choice function is unnecessary for this counterexample, but actual attainment at its witnesses is required and remains a proof obligation.
- **Actual Krylov minimization:** the subspace is the real span of `(AᵀA)^j Aᵀb` for all natural j<k. It gives the zero subspace at k=0 and admits all real linear combinations. `IsLSMRIterate` requires membership, minimal Euclidean normal residual over the entire subspace, and minimum Euclidean length among all minimizers. No minimizing property is assumed only for displayed vectors or rational competitors.
- **Zero start and exact termination:** `IsTerminatingLSMRRun` requires zero start, that minimization property for every index through N, nonzero normal residual at all earlier indices, and zero normal residual at N. The actual witness run is `[0,x₁,x₂,x₃]`; `exact_lsmr_run` must prove it and all three nonzero iterates. The fixed witness has nonzero final ordinary residual `(0,0,0,1)`, so testing normal residual rather than consistency is essential and done correctly.
- **Moore–Penrose meaning:** the relation imposes all four real Penrose equations with the correct rectangular orientations. `stacked` is `[A;(‖r‖/‖x‖)I]` on `Fin m ⊕ Fin n`; `stackedResidual` is the actual Euclidean stacked vector `[r;0]`. `IsApproximation` excludes x=0, uses the canonical exact-least-squares zero branch, and otherwise takes the norm of the actual `K P v` for a Penrose witness P. It does not define the error by a convenient rational expression. `approximation_values` requires existence and uniqueness of the resulting q at both witnesses, in addition to the exact squared values, so no choice of inverse witness changes either compared value.
- **Two genuine refutations:** the two monotonicity propositions retain arbitrary real dimensions, A,b and complete exact runs, without a universal full-rank hypothesis. They compare adjacent nonzero iterates. The fixed witnesses x₁,x₂ are adjacent and precede termination, so they also refute the canonical successive-nonzero formulation without any zero-index convention. `canonical_counterexamples` is the conjunction of two separate negations, not the weaker negation of a conjunction. `both_errors_increase` uses the same x₁,x₂ and demands both strict unsquared inequalities. Its run property is independently required by `exact_lsmr_run` for those same constants.
- **Terminal convention:** `terminal_errors_zero` demands both the actual attained zero spectral minimum and the stipulated zero approximation at x₃. The least-squares branch is `Aᵀ(b-Ax)=0`, not `b-Ax=0`.

These definitions contain the actual mathematical obligations. None packages the claimed counterexample values, bounds, run properties, or projection identities as assumptions. Every substantial relation has a nondegenerate witness obligation among the eight exports.

## Numerical and analytic certificate review

**Krylov run.** My independent solve reproduces x₁, x₂ and x₃, their coefficient vectors in `[g,Hg,H²g]`, the three displayed Gram determinants, `det V₃=-3049200`, residuals, normal residuals, and squared vector/residual norms. The Gram matrices are nonsingular; orthogonality gives global minimum residual over the real span, and injectivity gives uniqueness and thus minimum length. Earlier normal residuals are nonzero; the terminal one vanishes. The normal-residual squares decrease exactly as stated.

**New upper certificate.** I independently derive E from the manuscript's rational completion formula, recover every entry of `B_E/dE`, and check the exact perturbed normal equations. The completion denominator and both original direction inequalities agree with the source. Computing `G=(1979/2000)I−EᵀE` and the new T gives `det T=1` and exactly the displayed `TᵀGT=M/dM`. My independently computed diagonal-dominance margins are

```
11610303162792839972527905686,
2422484425274344247124223382031,
3388031261437186722083054351461.
```

All are positive. I also check the source's original three principal minors and expand the signed-square coefficient identity independently. Positive definiteness transfers through the invertible congruence. This proves an every-vector bound and, through the actual Euclidean operator norm, the required spectral upper bound; it does not replace it with an entrywise test.

**New lower certificate.** I independently reconstruct D₂, then the full K from `(5/6)C+(1/6)D₂−(99/100)I`, and check all four source principal determinants. Replacing K by `K* = K − dK/10000 I` corresponds exactly to the stronger threshold `9901/10000`. For `v=(10000,10,185,1287)`, my weighted margins are

```
6102817984650,
2612912207614679/10,
1352621546092623/20,
1055456050659373/100.
```

All are positive. I check that the ordinary diagonal-dominance margins of `diag(v)K*diag(v)` are exactly vᵢ times these margins, and independently expand its signed-square identity. Since every vᵢ is positive, congruence proves K* positive definite. It provides the stated uniform lower threshold for every unit vector.

The analytic passage still quantifies over **all real feasible E**. For nonzero new residual use its actual unit direction, the feasibility orthogonality, and both norm lower bounds before combining them. For zero new residual use `Ex=r` and the independently checked `ρ₂/s₂=274129000322/8026273307 > 9901/10000`. Thus that branch is not discarded. The explicit uniform gap is valid, and `IsLeast` independently preserves the source's actual minimum: there is no strict-infimum fallacy.

**Approximation values.** Exact diagonal-Gram evaluation reproduces both large rational squares and the complete cutoff chain through `503/500` and `1007/1000`. This arithmetic does not by itself prove the approximation formula. The implementation must establish actual Penrose witnesses/projector meaning, uniqueness of q, and the equality between that canonical norm and the rational squared formula; those obligations remain in the approved signatures. Nonnegativity of both errors is explicit and supports the required strict unsquared comparisons.

The general spectral-completion lemma, eigenvalue computation and Sylvester criterion need not be formalized merely to use these concrete certified matrices. The new congruence T and weighted certificate are explicitly disclosed as newly derived auxiliary arithmetic, distinct from Matthew J. Colbrook's original mathematical counterexample. Specializing these internal bounds to 4-by-3 matrices does not weaken the universal negative resolution.

## Scope, reuse and attribution

I checked the relevant pinned Mathlib norm, projection, finite-dimensional compactness and matrix-inverse APIs during [independent API research](statement-referee-1-evidence/api-checklist.md), retained in this review's evidence directory. Located reusable declarations include `ContinuousLinearMap.opNorm_le_bound`, `ContinuousLinearMap.le_opNorm`, `Submodule.starProjection`, `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`, `IsCompact.exists_isMinOn`, `FiniteDimensional.proper_real`, and `Matrix.PosDef.isUnit`, at Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The intended implementation should use existing continuous-linear-map norm bounds and compactness/projection APIs rather than reconstructing them. No general Moore–Penrose or Krylov implementation was located by full-source searches. The named norm wrapper has a necessary semantic role in the public target and genuine consumers; it is not a parallel invented norm. No proof implementation is yet present to assess for duplicated proof machinery.

The exact boundary and dossier preserve ID IE-17, the full original statement and manuscript, Matthew J. Colbrook's original proof attribution, and the requested George Stepaniants/Caltech formalization credit without a contact email in the new credit. The supplementary dense Hadamard variant remains in the original manuscript; it is not needed for either canonical refutation, and the dossier identifies that scope honestly.

## Exact reviewed hashes

| Boundary input | SHA256 |
|---|---|
| `NLA/IE17/Definitions.lean` | `5b151dd47f4ea35ac2ca0e51900b588ccac214ed9660704e98757cfb7cbe9344` |
| `Challenge.lean` | `9a3b525a5925e97778fbdedd5a8b0ac40c28064752deb9c86b633459b545a6e5` |
| `NUMERICAL_TARGETS.md` | `6a2f97e065892d1b1311d67f8ed3becccd8d7eb324f894278659f71d4a4b0a9d` |
| `comparator.json` | `7a674611023fec397d920eb7caaf951ad830bef470c498086556525260b79fe3` |
| `lakefile.toml` | `aeef3cd6cc700f3039502452436c47e782dd992535750077abadeea55b11939a` |
| `lake-manifest.json` | `f65f6e94b95f1638eac96a967aca5bef1fffecf581189571572c88e34d828c7c` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `reviews/initial-exact-check.py` | `b549473d30b371b28f9532db81015e4044bc492760900e3934e2db0c107babaf` |
| `reviews/initial-exact-check.json` | `19977a2934fd815aa63d7f0c5182c969be6b3650e94fd692281e95be13da827e` |
| `reviews/initial-source-hashes.json` | `616ba2680d5ecdc9038004b62a1a998e4f2614c4ee0fbc71115ed9770a7140bd` |

Canonical README SHA256: `53cba6429e84e1c8e055e10e5b7093f03ee0d1a94c8bf57f30ed150ae4cc08dc`. Complete manuscript SHA256: `d0e446f7b9ee5669c1beece9ca91a89387b2f8e340c19bca8254f556386efbcd`.

My [review evidence record](statement-referee-1-evidence/review-evidence.json), SHA256 `998c632df21a5b505afcf06b1954700d7c25a77396a0ae9c3f0d02fd42a03333`, records these final boundary hashes and my separate build/check evidence. Arithmetic checker SHA256: `d934aab7e51d86e80102f887285e5de08ce40f98ba9dc90c65e384234ddf2321`; exact output SHA256: `66feaf0a513d7bc0ee19dc56f3ecddd29d9c001a904cef567edc7eb41c4d674b`; independent statement-build log SHA256: `628774b066fce1d7019551a0b297f1575a1183ba2749bc96f6cbaa61b2033d3e`; retained API checklist SHA256: `2c9386945104094aea1ba4a62f12bccabc387838f33bcd8d90f7d895a304a15b`.

The statement gate may close after the required second independent approval. Any changed boundary or certificate bytes require re-review. Before status promotion, the complete actual proof must still receive independent source review and pass reproducible kernel-mode LeanCert, permitted-axiom and real Linux Comparator verification against this boundary.

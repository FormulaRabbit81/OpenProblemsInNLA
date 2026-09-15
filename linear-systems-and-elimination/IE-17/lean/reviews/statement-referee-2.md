# IE-17 independent pre-proof statement review — referee 2

**Verdict: APPROVE the exact ten-file boundary recorded below, including the complete mathematical statements and newly proposed numerical certificates.** No proof implementation, successful Comparator run, or completed formalization is asserted. The eight Challenge placeholders remain intentionally unproved.

Reviewer: **Codex AI agent `/root/existing_verification_audit`**, 2026-09-15. I independently read the complete canonical problem and recovered mathematical manuscript, prepared a pre-statement checklist before receiving the proposed definitions, and then inspected every actual definition, all eight signatures, the complete numerical dossier and dependency configuration. I wrote no target definitions or mathematical proof source. I independently recomputed the original and new numerical certificates and freshly typechecked the statement source. I did not use the other final statement referee's verdict. This is an independent AI-agent review applying the repository's Tau Ceti adaptation, not external human review or official endorsement.

## Exact reviewed identity

| Input | SHA-256 |
| --- | --- |
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

I recomputed all ten hashes and confirmed the core statement bytes were unchanged after my independent build. [Review evidence](statement-referee-2-evidence/review-evidence.json) retains the exact boundary and original-source hashes, actual eight Comparator names, checks performed and supporting evidence hashes.

The unchanged canonical README is SHA-256 `53cba6429e84e1c8e055e10e5b7093f03ee0d1a94c8bf57f30ed150ae4cc08dc`; complete current exported manuscript is `d0e446f7b9ee5669c1beece9ca91a89387b2f8e340c19bca8254f556386efbcd`; prior mathematical review is `c794511ab8a5977a0497ca84530d719745522e3aec5af566a6fc7b9d5e584903`. These agree with the preserved base `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. The manuscript's historical reviewed-body hash is a separate identity and must not replace the complete-file hash.

## Complete original target

The definitions preserve arbitrary real matrix dimensions, arbitrary real A and b, exact arithmetic, zero-start LSMR, its actual Krylov variational characterization, minimum length among minimizers, and first exact termination. Both displayed errors remain present, with b fixed and every real matrix perturbation allowed. The public result `canonical_counterexamples` is the conjunction of the two separate negations. It does not merely negate the conjunction of the original claims.

A single finite 4×3 counterexample suffices for both universal questions. The original matrix, right-hand side and all four iterates are exactly represented. Its zero row is permitted, while the separate full-column-rank theorem requires actual injectivity. The optional dense Hadamard variant is not needed to disprove either original question; the complete manuscript remains preserved. Universal original domains are retained in both monotonicity propositions, without imposing the witness's full-rank restriction on arbitrary inputs.

I also independently inspected the primary [Fong dissertation](https://web.stanford.edu/group/SOL/dissertations/david-fong-thesis-online.pdf): notation on printed p. 14 specifies the induced matrix 2-norm, definitions (4.1) and (4.5) on pp. 56–57 give the fixed-b error and stacked least-squares projection, and §7.2.1 on p. 118 conjectures both monotonicities. The [journal paper](https://web.stanford.edu/group/SOL/software/lsmr/LSMR-SISC-2011.pdf), §1.2, has a different usual matrix-norm convention. The dossier accurately preserves that distinction. This formalization must make no Frobenius-error claim.

## Norm and attained-minimum semantics

`spectralNorm` is explicitly the continuous-linear-map norm of `A.toEuclideanLin`, between `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`. I inspected the pinned Mathlib definitions: `toEuclideanLin` is `toLpLin 2 2`, acts as ordinary matrix multiplication in coordinates, and `toContinuousLinearMap` preserves the underlying linear map. `EuclideanSpace.real_norm_sq_eq` gives the sum of coordinate squares. Thus neither a plain-function sup norm nor a Frobenius/row-sum matrix norm has slipped in. The generic `spectralNorm_semantics` export explicitly requires the every-vector operator bound for all rectangular matrices.

`Feasible` uses `normalResidual (A+E) b x = 0`. This is the negative of the source's displayed normal-equation vector and has exactly the same zero set. `errorSet` ranges over **all real** E of the required size and stores their actual spectral norms. No rank, rationality, support, symmetry or completion-form restriction is present.

`IsOptimalError` is `IsLeast errorSet δ`. Its membership clause requires an actual attaining feasible perturbation; its lower-bound clause compares against every feasible perturbation. The existential `optimal_errors` theorem must prove these relations at both compared inputs and nonnegative values, not just exhibit certificate bounds. Hence there is no empty-set/totalized-infimum loophole and no assumed optimizer. Existence for the two actual inputs suffices for a finite negative resolution; a global arbitrary-input selection function is unnecessary. A proof must still supply true minimum attainment, for example by finite-dimensional compactness. The new uniform lower margin simplifies strictness but does not replace attainment.

The terminal export requires `IsOptimalError … witnessX₃ 0`. Exact least squares is correctly identified by **zero normal residual**, even though the terminal raw residual is `(0,0,0,1)`.

## Moore–Penrose approximation

`stacked` is exactly A above `(‖r‖₂/‖x‖₂)I`, with row index `Fin m ⊕ Fin n`. `stackedResidual` is `(r,0)` in the corresponding Euclidean space. This sum index is merely an explicit indexing of the original m+n rows.

`IsMoorePenrose` states all four correctly dimensioned real Penrose equations, including transpose symmetry of both products. `IsApproximation` requires x≠0, sets q=0 at an exact least-squares solution, and otherwise requires an actual four-equation MP witness P and the literal norm `‖KPv‖₂/‖x‖₂`. I inspected the elaborated definition to confirm that the nonzero-domain clause and conditional parse as intended.

The `approximation_values` export requires existence **and uniqueness of the actual q values** for both inputs, their nonnegativity, and the two exact squared fractions. Therefore the rational diagonal formula cannot be substituted as an unchecked definition, and a convenient generalized inverse cannot arbitrarily change q. A proof may derive the full-column formula or the unique orthogonal projector. At the actual nonterminal inputs, x and r are nonzero, η>0 and the stacked matrix has full column rank. The exact projector/scaled-inverse bridge remains necessary mathematical proof work after this gate.

The `terminal_errors_zero` export explicitly checks the canonical approximation convention at x₃ despite the nonzero raw residual. Divisions at excluded x=0 cannot generate the counterexample.

## LSMR, minimum length and termination

`krylov` is the full real span of `H^j g` for j<k, with H=AᵀA and g=Aᵀb. At k=0 this is the zero subspace. `IsLSMRIterate` requires membership, global Euclidean normal-residual minimization over the whole Krylov submodule, and minimum Euclidean length among all tied residual minimizers. The code does not mistake a normal-equation identity alone for minimization.

`IsTerminatingLSMRRun` includes x₀=0, this full minimizing predicate at **every** index, nonzero normal residual at every index below N, and zero normal residual at `Fin.last N`. The actual finite run has N=3. `exact_lsmr_run` additionally proves x₁,x₂,x₃≠0. The independent exact calculations show the required nonterminal residuals, terminal value and rank-three Krylov basis; the Lean proof still must connect those calculations to the minimizing predicate. Uniqueness for this full-rank example is a valid way to discharge the minimum-length clause.

Both monotonicity predicates compare adjacent indices with both iterates nonzero. The witness uses indices 1 and 2 of this very run, so it is valid regardless of any harmless ambiguity between adjacent iterations and filtering out zero iterates. `both_errors_increase` requires both strict **unsquared** inequalities and the exact source cutoff chains at the same x₁,x₂. The exact-run and counterexample exports connect these values to the algorithm, rather than merely giving two arbitrary vectors.

## Independent arithmetic and new auxiliary certificates

I independently reconstructed the exact integer A,b, rational x₁,x₂,x₃, residuals, normal equations, positive Krylov-image Gram determinants, norm squares, rational E, original upper/lower matrices and determinants, and both approximation fractions. The reviewer script [exact-check.py](statement-referee-2-evidence/exact-check.py) imports no submitted checker. Its [PASS record](statement-referee-2-evidence/exact-check.json) also independently verifies every new auxiliary certificate in the dossier:

- The explicit integer numerator B_E and denominator dE agree entry-for-entry with the original rational completion E. Its original completion denominator is positive and its actual perturbed normal equations vanish.
- The stated T has the explicit inverse obtained by replacing its first-row off-diagonal entries −18,23 with 18,−23. Direct multiplication gives identity. I computed `Tᵀ(κI−EᵀE)T=M/dM` exactly and obtained all three stated positive diagonal-dominance margins.
- I recomputed `K*=K−(dK/10000)I`, the weights `(10000,10,185,1287)`, and all four stated positive weighted margins. The zero-new-residual bound is exactly `274129000322/8026273307 > 9901/10000`.

The proposed mathematical use of these certificates is sound. The displayed finite sum-of-squares identity proves positivity of a symmetric strictly diagonally dominant matrix. Positive diagonal scaling transports the weighted lower certificate, and invertible congruence transports the upper certificate. The lower bound covers **every real feasible E**, treating nonzero and zero new residual separately. Its explicit 9901/10000 margin exceeds 99/100, avoiding a strict-infimum mistake. None of these computations weakens the spectral norm, optimization domain or LSMR target. The new auxiliary T/weights are correctly disclosed as newly derived, without attributing them to Colbrook's manuscript.

These Python checks are exact finite arithmetic diagnostics, not formal proofs of matrix positivity implications, actual norm bounds, MP identities or attainment. Those analytic and semantic connections remain required Lean proofs.

## Typecheck, Comparator boundary and attribution

I copied the five core source/build files into a fresh local project directory without IE-17 object files, reused the existing pinned dependency packages, and ran pinned Lean 4.33.1 `lake build Challenge`. Both Definitions and Challenge rebuilt successfully; exit **0**, with precisely eight expected specification-hole warnings. [Build log](statement-referee-2-evidence/fresh-statement-build.log), SHA-256 `062ffd23d0e2e2822d152fa234f1dbf24a540df978780f65c572f3920ece865f`. I separately ran [StatementAudit.lean](statement-referee-2-evidence/StatementAudit.lean) and inspected the [elaborated definitions and eight target types](statement-referee-2-evidence/elaborated-boundary.log); exit **0**. This was a macOS statement build using pinned dependency objects, not Linux verification or proof completion.

The manifest contains immutable Git dependency revisions; LeanCert is pinned at `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Lake's default target is still Challenge. Comparator selects exactly the eight declarations present in Challenge, without replaceable definition holes, and permits only `propext`, `Classical.choice`, `Quot.sound`. No custom axiom, native proof, placeholder or unsafe declaration appears in Definitions. Only the separate Challenge contains its eight intentional holes. A later proof must use LeanCert in kernel mode and supply genuine permitted-axiom and Comparator evidence; none exists at this stage.

The complete original target and permanent ID remain unchanged. The source counterexample retains **Matthew J. Colbrook** attribution; new formalization headers distinguish **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, disclose substantial Codex assistance, and add no contact email. Original archived proof/source bytes and historical attribution must remain preserved.

**APPROVE at the exact hashes above.** The mathematical and numerical statement gate may be sealed after the other independent statement approval. Canonical status remains **Solved**; proof implementation, independent final review, permitted-axiom checks, fresh Linux Comparator/kernel verification and publication review are still outstanding.

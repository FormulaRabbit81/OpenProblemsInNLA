# IE-17 Norms module: independent interim review

Reviewer: **Codex AI agent `/root/existing_verification_audit`**, 2026-09-15; non-implementing independent statement/final referee. **Interim verdict: sound at the hashes below; no semantic, type-instance or attainment gap found.** This covers only `Norms.lean`, not the complete IE-17 proof or any publication/status gate.

## Identity and independent checks

Reviewed project: `/private/tmp/nla-formalization-ie17-20260915/linear-systems-and-elimination/IE-17/lean`, following frozen boundary commit `5d9ae3c9`.

- `NLA/IE17/Norms.lean`: SHA-256 `c9af7b25650fd4873e6559794ed1a1c927ed38cda46bbbf987e323b8750d3137`.
- Frozen `NLA/IE17/Definitions.lean`: `5b151dd47f4ea35ac2ca0e51900b588ccac214ed9660704e98757cfb7cbe9344`.

I read the entire module and relevant pinned Mathlib definitions. I copied this exact module into my separate statement-review project and ran pinned Lean 4.33.1 `lake build NLA.IE17.Norms`. It freshly compiled the module and exited **0** without warnings. I then ran an independent audit printing the axiom closure of all **13** module lemmas, the exact generic minimum-existence type, and its elaborated proof. The audit exited **0**; every closure uses only `propext`, `Classical.choice`, `Quot.sound`.

Scratch evidence under `ie17-fresh-statement/`:

- `norms-build.log`: SHA-256 `5129eca0282d56b77cca3c1d17f44e69fe1bacf396cf5ae1a897c713973b1b26`.
- `NormsInterimAudit.lean`: `185b58882fa56609f09a9e7d0bf227322325449f2ca732a22b27dca59c185485`.
- `norms-axioms.log`: `8c13dd7d10ea0ab665579417d6fce83151d5a29d72fa3a4bbcd16acf2acfb351`.
- `IE17-norms-interim.json` beside this report records the parsed closures and hashes.

The source and frozen Definitions hashes were checked again after those commands and remain unchanged. This is an independent local module-source build using existing pinned dependency objects; it is not fresh Linux Comparator verification.

## Norm meaning and type instances

The scoped instance is specifically `Matrix.Norms.L2Operator`. The lemma `spectralNorm_eq_l2` is proved by reflexivity, certifying that the matrix norm used throughout this module is definitionally the frozen continuous-linear-map Euclidean operator norm. The pinned Mathlib L2 construction explicitly transports the norm from maps between Euclidean spaces and retains the standard finite-dimensional topology. There is no entrywise, Frobenius or row-sum substitution.

`apply_norm_le` uses the actual continuous linear operator bound. `spectralNorm_le_iff` proves both directions with the required nonnegative c; it is not a circular norm definition. The transpose norm equality applies the genuine L2 adjoint/transpose theorem for real matrices. The derived transpose-application bound therefore has the correct dimensions and exact norm constant.

## Feasibility, closedness and genuine attainment

`feasible_neg` supplies an actual feasible perturbation E=−A for every real A,b,x. `feasible_zero_iff` uses the actual fixed-b normal-residual definition. `optimal_zero_of_normalResidual_zero` constructs membership with E=0 and proves a universal lower bound from nonnegativity of every perturbation norm. It correctly applies to inconsistent least-squares solutions with nonzero raw residual.

The continuity proof treats E↦A+E, transpose, and both Euclidean linear-map applications explicitly. It does not infer closedness from a restricted finite family of perturbations. Consequently `isClosed_feasible` concerns the complete all-real matrix feasible set from the frozen definition.

For `exists_optimal_error`, the compact set is exactly the intersection of that closed feasible set with the **spectral-norm** closed ball centered at zero with radius ‖A‖₂. The witness −A lies in the intersection because its norm equals ‖A‖₂. The finite-dimensional compactness theorem supplies a norm-minimizing E₀ in that set.

The proof then establishes global minimality against **every** real feasible E: if ‖E‖₂≤‖A‖₂ it belongs to the compact set and the actual minimizer comparison applies; otherwise ‖E₀‖₂≤‖A‖₂<‖E‖₂. The resulting `IsLeast errorSet (spectralNorm E₀)` includes both an explicit attaining E₀ and that global bound. No infimum totalization, unattained endpoint, hidden optimizer hypothesis or constraint on the perturbation's structure is used.

The theorem retains arbitrary m,n,A,b,x, including zero dimensions, zero matrices and zero iterates. It does not divide by x or assume rank, inconsistency, or nonzero input. The same compactness/nonempty argument remains valid when the ball radius is zero.

## Disposition

**Sound interim module review.** No source edits requested. This result supplies the previously identified genuine-attainment obligation and usable true-norm bounds. The all-perturbation lower bridge, actual LSMR/MP semantics, numerical certificates, eight final exports and authoritative verification remain outside this bounded review. This report must not be described as full-target approval or used alone to promote IE-17 status.

# MI-13 Gram-basis scalar-conversion repair candidate

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance. All prior mathematical and code attribution, including the canonical Nobori/Audenaert credits, remains unchanged. No email is included.

## Scope and status

This packet changes only the final `simpa` in `NLA/MI13/GramBasis.lean`'s `ordered_gram_basis` body. Both exact frozen signatures, the positive-image extension body, imports, options, axiom reports, and kernel trust assertions are unchanged. All 13 frozen inputs were rehashed successfully. No Lean, Lake, cache, or compiler command was executed by this source author. Root must test the candidate using the one-process, one-thread, 4096 MiB serial local runner. This packet makes no complete-target, Comparator, sandbox, publication, or count claim.

The actual prior failure is preserved in `evidence/development-23/`. Its receipt binds the original GramBasis source to SHA-256 `b07caae9da98fbb7a0b220e54c9fcce06d6b641c3b49705d87ea30b884fba4ce`. The compiler returned 1 at the final conversion in `ordered_gram_basis`; the downstream trust assertion consequently rejected its error-recovery `sorryAx`. The unchanged `positive_image_extension` axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`. The failed run is not proof acceptance.

## Mathematical and scalar details

For every natural dimension r, the actual complex Euclidean operator T has symmetric positive Gram operator T* T. Mathlib's eigenvector basis sorts the real Gram eigenvalues in decreasing order, including multiplicity. Its eigenvector equation has scalar `(eigenvalue : RCLike field)`. The actual singular-value API identifies that real eigenvalue with `T.singularValues i ^ 2`. The frozen `GramBasis` instead spells the final scalar as the square of the ordinary complex cast of `singularValue A i.val`. No positivity hypothesis, distinct-eigenvalue assumption, SVD oracle, or nonempty-dimension hypothesis is added.

There is a concrete source-level distinction hidden by the displayed up-arrow: the generic spectral API uses `RCLike.ofReal : ℝ → ℂ`, defined through `Algebra.cast`, while the frozen complex scalar uses `Complex.ofReal`. Pinned `Analysis/Complex/Basic.lean:357` gives the exact bridge `RCLike.ofReal_eq_complex_ofReal`, proved by `rfl`. The previous proof used only the generic `RCLike.ofReal_pow`; the candidate explicitly rewrites the generic cast to `Complex.ofReal` and then invokes `Complex.ofReal_pow`. The Gram operator's composition and the local singular-value abbreviation are simplified as before.

This explains a plausible hidden elaboration difference and removes that difference explicitly. The development-23 log does not print implicit arguments, so it does NOT establish that this cast alone is the actual blocker; another implicit instance could remain. Root has agreed to run a bounded `pp.all` diagnostic in its serial compiler if this candidate fails. No causal certainty or successful elaboration is claimed here.

## Pinned API evidence

Eight selected primary Mathlib files were fetched from the literal commit `0df444a360eaa60ab8c11dca51a86af692955474` and byte-compared with the shared read-only source. `PRIMARY-BINDINGS.json` records exact URLs, hashes, copied files, and read line ranges. The relied-on APIs are:

- `LinearMap.IsSymmetric.eigenvectorBasis` and `apply_eigenvectorBasis` in `Analysis/InnerProductSpace/Spectrum.lean:300,325`.
- `LinearMap.sq_singularValues_fin` in `Analysis/InnerProductSpace/SingularValues.lean:128`.
- `RCLike.ofReal` and `ofReal_pow` in `Analysis/RCLike/Basic.lean:97,204`.
- `RCLike.ofReal_eq_complex_ofReal` in `Analysis/Complex/Basic.lean:357`.
- `Complex.ofReal_pow` in `Data/Complex/Basic.lean:665`.
- `LinearMap.isSymmetric_adjoint_comp_self` in `Analysis/InnerProductSpace/Adjoint.lean:756`.
- The unchanged extension proof's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` in `Analysis/InnerProductSpace/PiL2.lean:1047`.

These selected-source checks are not a transitive proof audit. The before/after source copies, diff, exact frozen headers, input bindings, and static checks are sealed by `MANIFEST.json`. Compiler outputs must be recorded by root against the candidate hash, separately from this source-author packet. Remaining SVD/normalized-image and complete MI-13 obligations are outside this bounded repair.

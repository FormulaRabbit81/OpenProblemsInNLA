## Change

Add complete Lean verification of SF-01's original Newton preservation theorem. Credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, for formalization; preserve Matthew J. Colbrook's mathematics and Sidney Holden's reused IV03 code credit. Please merge this individual submission into `ajt60gaibb/OpenProblemsInNLA:main`.

## Mathematical evidence

`NLA.SF01.canonical_newton_preservation` covers every real positive-diagonal nonsingular H-matrix, every positive dimension and every exact Newton step from X0=A, and proves invertibility at each step. The original full complex spectral-radius definition is retained through proved spectral/weight bridges. No symmetry, normality, positive entries, finite iteration cap or supplied rational representation is assumed. Scaled/affine and Halley extensions are not additional formal claims. Primary source: Colbrook's retained SF-01 manuscript, Theorem 1, specialized to the complete original target.

The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3312b0795873cfecade03fa421a5433651d47674/matrix-functions-and-stability/SF-01/lean/Solution.lean) passed [actual non-root Linux run 35175258802](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35175258802/job/105055517720): all 271 inputs, all 24 Comparator contracts, default-kernel replay, standard transitive axioms and per-project rejection/isolation controls. The kernel-mode LeanCert half-positivity certificate is actually consumed. Two complete nonauthor source reviews and the independent runtime audit are retained with explicit scopes. Local Lean development and GitHub verification are distinct; an evidence audit is not another execution.

Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926 are pinned. Run `lake build` in `matrix-functions-and-stability/SF-01/lean`; the README includes full shared Linux checker commands, source correspondence, raw logs and axiom reports.

## Documents checked

DRAFT: The canonical README, Lean metadata/evidence, RESOLVED entry and standalone formalization note are prepared. Independent publication review, PDF rendering/visual inspection, catalog/ID safeguards and later publication/upstream checks are still pending. Replace this paragraph with measured results before posting. Original IDs, mathematical targets and the shared original manuscript are unchanged; no email is published.

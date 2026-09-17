## Change

Add complete Lean verification of RA-02's negative answer to the polynomial trace-error question after exactly the target rank of RPCholesky pivots. Credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, for formalization and verification; preserve Matthew J. Colbrook's original mathematics and all prior source authorship. This is an individual submission for `ajt60gaibb/OpenProblemsInNLA:main`.

## Mathematical evidence

`NLA.RA02.no_polynomial_trace_factor` negates the original assertion for real constants `C > 0`, `p >= 0`, all positive dimensions, all complex Hermitian PSD matrices, and every integer `1 <= r <= n`. `NLA.RA02.universal_counterexamples` supplies a positive-definite witness of order `r + 1`, with positive actual ordered eigenvalue tail and strict violation after exactly `r` pivots. The normalized law includes every ordered history. The sufficient finite factor `2^r/3` resolves this entire target; sharp limiting, entrywise-positive, correlation-matrix, LU and oversampling extensions are not additional formal claims.

Primary mathematical source: Matthew J. Colbrook, [*Sharp worst-case factors for randomly pivoted Cholesky and LU*](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/ce47b5630bf3680d9211131c3a43825b022c139a/references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.tex), Theorem 1 and Corollary 3. The unchanged shared manuscript retains mathematical authorship; the formal proof uses the separately documented finite arrowhead route, an alternative proof of the same negative answer. Full statement correspondence and all 27 declarations are retained in the Lean project.

The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/26dc080e47b75a3aaf2e75fc2a282d0b8f4a4bbb/randomized-and-low-rank-approximation/RA-02/lean/Solution.lean) at `26dc080e47b75a3aaf2e75fc2a282d0b8f4a4bbb` passed [actual non-root Linux run 35175272827](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35175272827/job/105055587640): all 220 submitted inputs, all 27 Comparator contracts, default-kernel replay, the three standard transitive axioms and the required rejection and sandbox controls. The sole kernel-mode LeanCert certificate `Real.exp 1 <= 3` is consumed by the denominator bound, actual-tail estimate and final counterexample. Two complete nonauthor source reviews and an independent runtime audit are retained with exact scopes. Local macOS development and GitHub Linux verification are distinct executions; evidence audits are not additional runs.

Pins: Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Run `lake build` in `randomized-and-low-rank-approximation/RA-02/lean`; its README gives the shared Linux bootstrap, selftest and verify commands, complete logs and measured axiom report. No official Tau Ceti endorsement or human peer review is claimed.

## Documents checked

DRAFT FOR THE COORDINATOR: The canonical README and TeX, standalone formalization note, Lean README and metadata/evidence/review index, and RA-02 RESOLVED entry are prepared in a private overlay. Static v0.4 schema and the unchanged repository completed-manifest validator pass for all 27 declarations. The original canonical target, proof sources, permanent ID/path and shared mathematical manuscript remain unchanged; no email is published. Replace this paragraph and the checklist below with measured final results before posting.

- [ ] Independent publication-overlay review accepted.
- [ ] Both affected PDFs rendered and visually inspected; links and text checked.
- [ ] Permanent-ID validator, catalog regeneration and required numbering tests completed against the published base.
- [ ] Exact publication-commit execution authenticated, with actual workflow selection checked.
- [ ] Individual upstream PR created and its actual checkout verification authenticated.

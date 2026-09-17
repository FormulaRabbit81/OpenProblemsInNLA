# IE-02 — Is the ideal GMRES bound sharp for every Jordan block?

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified  
**Last checked:** 2026-09-17  

**Rating rationale:** Historical assessment retained: challenging because the remaining Jordan-block minimax cases require control of multiple extremal singular vectors; specialist impact reflects a structural test case for GMRES theory.

## Resolution — 2026-09-11

**Solved affirmatively.** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, proves the displayed equality for every $`n\ge2`$, $`1\le k< n`$, and nonzero complex $`\lambda`$, with complex polynomials and starting vectors. No divisibility or eigenvalue-regime case remains open.

[Theorem 1 and its proof](solution.md) establish the exact original target. The stronger Theorem 6 proves affine minimax equality for triangular Toeplitz matrices: finite Carathéodory–Fejér interpolation describes the maximal singular subspace, and scalar spectral factorization preserves every complex GMRES orthogonality equation in one unit vector. [Proof PDF](solution.pdf) · [Standalone XeLaTeX source](solution.tex).

The complete AI-assisted proof passed a separate [independent Codex-agent review](../../references/stepaniants-ie02-2026-09-11/verification/IE-02-independent-review.md). That earlier audit was automated-agent verification; the later Lean verification is recorded below. [Submission record, preserved source and public eligibility check](../../references/stepaniants-ie02-2026-09-11/README.md). The original problem statement and permanent ID remain unchanged; the earlier special cases and status checks below are retained as history.

## Lean proof and verification evidence - 2026-09-17

**The complete original target is Lean verified.** `NLA.IE02.canonical_jordan_minimax` proves the result in the [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/9dc46f23457fed8396ad9f6a77677efe30c87df4/linear-systems-and-elimination/IE-02/lean/Solution.lean) at revision `9dc46f23457fed8396ad9f6a77677efe30c87df4`. Ideal and worst-case GMRES are equal for every complex upper Jordan block in the original range: n at least 2, nonzero complex eigenvalue, and 1 at most k less than n. The polynomial minima and sphere maximum use actual Euclidean norms, with attaining witnesses. Finite Schur recursion, scalar spectral factorization, complex gradient convexity and uniform descent prove the affine minimax result and transport it to the actual upper Jordan block. No interpolation or minimax oracle is assumed.

[Linux run 35230302016](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35230302016/job/105232489885) passed all 50 exact Comparator contracts, Lean's default kernel, transitive permitted-axiom checks and actual rejection/isolation controls. [Retained evidence](lean/verification/linux-35230302016/README.md) distinguishes the preceding local macOS compilation from the final GitHub execution and the subsequent independent evidence audits. Two full nonauthor mathematical reviews and the operational reviews are linked in the [project instructions](lean/README.md).

A genuine kernel-mode LeanCert certificate proves the positive-half bound consumed by the symbolic descent estimate. Factorization, root selection and extrema are symbolic, without an interval grid or sampling. All exported results use only `propext`, `Classical.choice` and `Quot.sound`. The project pins Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Run `lake build` in `linear-systems-and-elimination/IE-02/lean` to check locally; the shared harness runs the separate non-root Linux Comparator checks.

Formalization and verification submission: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Prior mathematical and library authorship remains as credited below and in [source correspondence](lean/SourceCorrespondence.md). Substantial OpenAI Codex assistance and scoped independent AI-agent reviews are disclosed; no external human peer review is claimed. Later publication and upstream PR checks remain pending and will be recorded separately.

## Problem statement

For $`n\geq2`$ and $`\lambda\in\mathbb C\setminus\{0\}`$, let $`J_n(\lambda)=\lambda I+N`$, where $`N_{i,i+1}=1`$ and all other entries of $`N`$ vanish. Let $`\mathcal P_k=\{p\in\mathbb C[z]:\deg p\leq k,\ p(0)=1\}`$. Define

```math
\psi_k(J)=\max_{\|v\|_2=1}\min_{p\in\mathcal P_k}\|p(J)v\|_2,
\qquad
\phi_k(J)=\min_{p\in\mathcal P_k}\|p(J)\|_2.
```

Prove or disprove $`\psi_k(J_n(\lambda))=\phi_k(J_n(\lambda))`$ for every $`1\leq k< n`$. The maximum describes the slowest possible GMRES residual reduction, whereas the minimum over operator norms is the ideal bound. The familiar inequality $`\psi_k\leq\phi_k`$ does not answer the question. A single Jordan block is a published structural test case, not a claim about all nonnormal matrices.

## References

Tichý, Liesen, and Faber, [*On worst-case GMRES, ideal GMRES, and the polynomial numerical hull of a Jordan block*](https://etna.ricam.oeaw.ac.at/volumes/2001-2010/vol26/abstract.php?pages=453-473), ETNA 26 (2007), 453–473, §1 conjecture and subsequent special cases. Faber, Liesen, and Tichý, [*Matrix best approximation in the spectral norm*](https://arxiv.org/abs/2506.09687), published in LAA 733 (2026), §§4–5.

## Earlier status check — 2026-09-08

Searches for `Jordan block ideal GMRES equality proved 2026` and `site:arxiv.org GMRES Jordan block` found the original partial results and the 2026 general approximation paper, but no resolution of the displayed Jordan-block equality. The latter paper's doubling theorem changes the matrix and does not by itself establish this statement.

## Audit update — 2026-09-10

Rechecked the [author copy of Tichý–Liesen–Faber](https://www.karlin.mff.cuni.cz/~ptichy/download/public/TiLiFa2007.pdf), especially §§3–5: Corollary 4.4 proves equality whenever $`k`$ divides $`n`$, with additional eigenvalue regimes proved elsewhere in those sections. These are substantive parts of the displayed target. The [2025/2026 approximation paper](https://arxiv.org/html/2506.09687) and targeted Jordan-block/ideal-GMRES searches did not supply the remaining cases; its doubling construction changes the input matrix.

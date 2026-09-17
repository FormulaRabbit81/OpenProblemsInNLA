# SF-01 — Preservation of real H-matrix structure by Newton square-root iterates

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because convergence does not control comparison-matrix structure at each iterate; specialist impact concerns square-root algorithms for H-matrices.  
**Status:** Lean verified  
**Last checked:** 2026-09-11  

## Lean proof and verification evidence

**The complete original Newton target is Lean verified, 2026-09-17 (UTC).** The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3312b0795873cfecade03fa421a5433651d47674/matrix-functions-and-stability/SF-01/lean/Solution.lean) at `3312b0795873` passed [actual non-root Linux run 35175258802](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35175258802/job/105055517720). The [retained logs and source hashes](lean/verification/linux-35175258802/README.md) and [independent runtime review](lean/reviews/canonical-runtime/REVIEW.md) cover all 271 submitted inputs, all 24 Comparator targets, default-kernel replay, standard transitive axioms and the actual rejection/isolation controls.

`NLA.SF01.canonical_newton_preservation` proves that the original exact recurrence, initialized at $`X_0=A`$, is defined and preserves the nonsingular real H-matrix property and strictly positive diagonal for every positive dimension and every iteration. The comparison matrix and full complex algebraic spectral radius match the original definitions. Spectral-to-weight and weight-to-spectral bridges are proved; no symmetry, normality, positive-entry, bounded-iteration or supplied-representation premise is added. See the [independent contracts](lean/Challenge.lean) and [source correspondence](lean/SourceCorrespondence.md). The manuscript's scaled/affine initializations and Halley extensions are outside this formal claim.

Formalization and verification: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains original mathematical authorship. **Sidney Holden** retains authorship and Apache-2.0 credit for two unchanged, actually imported [IV-03 source files](lean/REUSE-IV03.md). AI assistance and scoped independent agent reviews are disclosed; no official Tau Ceti or human endorsement is claimed.

The project pins Lean 4.33.1, [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and [LeanCert](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926). A consumed kernel-mode LeanCert certificate proves $`0< 1/2`$; the dimension, matrix and iteration arguments are symbolic, with no interval subdivision. All 24 exported theorems use only `propext`, `Classical.choice` and `Quot.sound`. Run `lake build` in `matrix-functions-and-stability/SF-01/lean`; the [project README](lean/README.md) gives the complete Linux checker commands and separates the actual local macOS development from the GitHub execution. Later publication-commit and upstream PR runs are separate checks.

The [formalization note](solution.pdf) and [TeX source](solution.tex) record the scope and authorship. The original mathematical resolution remains unchanged below.

<!-- colbrook-matrix-functions -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

Every exact Newton square-root iterate initialized at $`X_0=A`$ remains a real nonsingular H-matrix with positive diagonal. The theorem includes arbitrary positive scalar scaling and nonnegative affine initializations, with one diagonal-dominance weight for all iterates; it also proves the corresponding Halley preservation result.

The complete target is resolved. Its former difficulty rating is historical; the original statement, references and dated audits remain below.

**Primary reference:** [complete authored PDF](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/SF-01.pdf), [standalone TeX](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/SF-01.tex), **Theorem 1; Corollary 5 gives the Halley extension**. [Independent proof review](../../references/colbrook-matrix-functions-2026-09-11/verification/reviews/SF-01-review.md) · [Authorship and submission record](../../references/colbrook-matrix-functions-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-matrix-functions -->

## Problem statement

For a real square matrix $`Y=(y_{ij})`$, define its comparison matrix by
$`\mathcal M(Y)_{ii}=|y_{ii}|`$ and
$`\mathcal M(Y)_{ij}=-|y_{ij}|`$ for $`i\ne j`$.
Call $`Y`$ a nonsingular H-matrix when
$`\mathcal M(Y)=sI-B`$ for some entrywise nonnegative $`B`$ and real
$`s>\rho(B)`$.

Let $`n\ge1`$ and let $`A\in\mathbb R^{n\times n}`$ be a nonsingular H-matrix
with $`a_{ii}>0`$ for every $`i`$. Consider the exact-arithmetic recurrence

```math
X_0=A,\qquad X_{k+1}=\tfrac12(X_k+X_k^{-1}A),\qquad k\ge0.
```

Is every $`X_k`$ a nonsingular H-matrix with strictly positive diagonal?
The known existence of these iterates and their convergence to the principal
square root do not themselves establish the requested structure at every step.

## References and status

N. J. Higham,
[*Functions of Matrices: Theory and Computation*](https://epubs.siam.org/doi/10.1137/1.9780898717778.ch6)
(SIAM, 2008), §6.3, equation (6.12), §6.8.3, and Research Problem 6.25,
p. 170. The author's
[errata](https://nhigham.com/errata-for-functions-of-matrices-theory-and-computation/)
correct the surrounding p. 161 theorem to real H-matrices; that restriction is
adopted here. L. Lin and Z.-Y. Liu,
[*On the Square Root of an H-matrix with Positive Diagonal Elements*](https://doi.org/10.1023/A:1012931928589),
*Annals of Operations Research* 103 (2001), 339–350, concern the square root itself.
Searches on 2026-09-08 for the problem number and Newton/H-matrix
structure preservation found no resolution. The recent
[Bini–Iannazzo–Meini–Meng preprint](https://arxiv.org/html/2605.21679)
(20 May 2026), §§3–4, treats M-matrices, a narrower class. The latest explicit
open-problem evidence found for this assertion remains the 2008 book.

## Audit — 2026-09-10

Rechecked the [2026 M-matrix paper, §§4 and 4.2](https://arxiv.org/html/2605.21679): its normalized nonsingular M-matrix class has structure-preserving Newton iterates starting from $`A`$. This is a substantive subfamily of the displayed target. Searches for Higham's Problem 6.25 and H-matrix iterate preservation found no general answer; the surviving H-matrix question still has historical evidence.

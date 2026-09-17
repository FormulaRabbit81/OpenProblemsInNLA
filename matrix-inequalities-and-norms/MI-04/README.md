# MI-04 — A universal block-norm characterization of essentially Hermitian matrices

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified  
**Last checked:** 2026-09-16

**Rating rationale:** The universal converse needs new control of positive block completions; its immediate impact is a specific numerical-range characterization.

## Resolution — 2026-09-11

**Affirmative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

The universal positive-block operator-norm property holds exactly when the off-diagonal block is essentially Hermitian. The proof applies in every finite dimension without invertibility or distinct-singular-value assumptions.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-04-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Lean proof and verification evidence - 2026-09-16

**The full original implication is Lean verified.** The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/63340ef17139606dce03c4d9000288129b773157/matrix-inequalities-and-norms/MI-04/lean/Solution.lean) at revision `63340ef17139` passed [Linux run 35150473054](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35150473054/job/104977317684). The [retained evidence](lean/verification/linux-2026-09-16/README.md) and [independent runtime audit](lean/reviews/canonical-runtime/REVIEW.md) cover all 233 submitted inputs, all 21 exported statements, default-kernel replay, Comparator, permitted transitive axioms and actual rejection/isolation controls.

Declaration: `universal_positive_block_essentially_hermitian` in namespace `NLA.MI04`.

The [main Lean theorem](lean/NLA/MI04/Conclusion.lean) assumes the stated operator-norm bound for every genuine positive-semidefinite block completion and constructs an actual Hermitian matrix and complex affine coefficients. Every positive finite complex dimension is included, with singular completions, scalar and zero matrices and repeated spectral values. The manuscript's stronger converse and four-way equivalence are outside the formal claim. The [frozen definitions and 21 targets](lean/Challenge.lean) and [source correspondence](lean/SourceCorrespondence.md) record this comparison.

Formalization and verification submission: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains mathematical proof credit. Substantial OpenAI Codex assistance and scoped independent AI-agent reviews are disclosed; no human peer-review or new priority claim is made.

The project pins Lean 4.33.1, [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and [LeanCert](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926). Its consumed LeanCert certificate proves $`0<1/4`$ in kernel mode without interval subdivision. Every exported result has only `propext`, `Classical.choice` and `Quot.sound` as transitive axioms. Run `lake build` in `matrix-inequalities-and-norms/MI-04/lean`; the [project instructions](lean/README.md) give the full non-root Linux check. Later publication and upstream checks are separate from the immutable proof run.

## Problem statement

Let $`n\ge1`$ and $`X\in\mathbb C^{n\times n}`$. Suppose that for every pair of Hermitian $`A,B\in\mathbb C^{n\times n}`$ for which

```math
H=\begin{bmatrix}A&X\\X^*&B\end{bmatrix}\succeq0,
```

one has $`\|H\|_2\le\|A+B\|_2`$, where $`\|\cdot\|_2`$ is the operator norm. Must there exist a Hermitian $`K`$ and scalars $`\alpha,\beta\in\mathbb C`$ with $`X=\alpha K+\beta I_n`$?

Such an $`X`$ is called essentially Hermitian; equivalently its numerical range $`\{v^*Xv:\|v\|_2=1\}`$ lies in an affine line.

## Why it matters

The question characterizes exactly when off-diagonal coupling in a positive block matrix can always be ignored in a particular spectral-norm bound. It connects a numerical-range geometry condition to a universal norm estimate.

## References

1. J.-C. Bourin and E.-Y. Lee, *Eigenvalue inequalities for positive block matrices with the inradius of the numerical range*, arXiv:2111.15180v1 (30 November 2021), Conjecture 3.3, Theorem 3.2, and Proposition 3.4. [Primary text](https://arxiv.org/html/2111.15180).
2. T. Hayashi, *On a norm inequality for a positive block-matrix*, Linear Algebra and its Applications 566 (2019), 86–97, Theorem 2.5. [Preprint](https://arxiv.org/abs/1808.00181), [DOI](https://doi.org/10.1016/j.laa.2018.12.027).

## Status check — 2026-09-10

The latest arXiv version of reference 1 remains v1. Hayashi proves normality under additional invertibility and distinct-singular-value assumptions, not the stated conclusion in full generality. A Frobenius-norm variant characterizes normality and is already proved. Searches included `Bourin essentially Hermitian conjecture`, `universal positive block matrix norm Hayashi conjecture`, and `essentially Hermitian conjecture proof 2025 2026`. No later resolution of Conjecture 3.3 was located. A 2025 result on decomposable numerical ranges settles a different conjecture.

**Audit update (2026-09-10):** Rechecked Bourin–Lee Conjecture 3.3 and searched for subsequent essentially-Hermitian characterizations. The Frobenius-norm theorem has a different norm and conclusion; no resolution of the operator-norm converse was located. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

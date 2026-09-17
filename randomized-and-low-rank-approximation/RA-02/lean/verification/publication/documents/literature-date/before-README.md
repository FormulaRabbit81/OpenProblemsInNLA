# RA-02 — Polynomial trace-error factor after exactly the target rank of pivots

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because removing exponential loss without oversampling requires sharper adaptive-pivot analysis; community impact is rank-efficient PSD approximation.  
**Topic:** randomized factorization; approximation guarantees  
**Last checked:** 2026-09-17  
**Status:** Lean verified  

<!-- colbrook-random-pivoting -->
## Resolution — 2026-09-11

**Negative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Theorem 1 and Corollary 3 disprove the existence of constants $`C,p`$ giving the displayed polynomial bound after exactly $`r`$ pivots. For every fixed $`r\ge1`$, real entrywise-positive positive-definite matrices of order $`r+1`$ approach the sharp expected trace-error ratio $`2^r`$ as a parameter tends to zero. Choose $`r`$ first and then the parameter; no limit uniform in $`r`$ is needed. The result does not address oversampling (RA-01).

[Complete manuscript](../../references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.pdf) · [TeX](../../references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.tex) · [Independent complete-source PASS review](../../references/colbrook-random-pivoting-2026-09-11/verification/reviews/RA-02-review.md) · [Authorship, exact checks and provenance](../../references/colbrook-random-pivoting-2026-09-11/README.md).

The original manuscript audit is independent agent review, not external human peer review. The separate Lean verification below covers the complete original RA-02 target. AI assistance is disclosed; no priority claim is made. The original statement and audits remain below; ratings are historical.
<!-- /colbrook-random-pivoting -->

## Lean proof and verification evidence

**The complete original negative target is Lean verified, 2026-09-17 (UTC).** The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/26dc080e47b75a3aaf2e75fc2a282d0b8f4a4bbb/randomized-and-low-rank-approximation/RA-02/lean/Solution.lean) at `26dc080e47b7` passed [actual non-root Linux run 35175272827](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35175272827/job/105055587640). The [retained evidence](lean/verification/linux-35175272827/README.md) and [independent runtime review](lean/reviews/canonical-runtime/REVIEW.md) authenticate all 220 submitted inputs and all 27 Comparator contracts, default-kernel replay, standard transitive axioms, and the required rejection and sandbox controls.

For every real $`C>0`$ and $`p\ge0`$, `NLA.RA02.universal_counterexamples` constructs a positive-definite complex matrix of order $`r+1`$, for some $`r\ge1`$, with positive actual spectral tail and a strict violation after exactly $`r`$ pivots. `NLA.RA02.no_polynomial_trace_factor` negates the full original assertion over all positive dimensions and complex Hermitian PSD matrices. The proof establishes the normalized adaptive law on every ordered history and uses the actual decreasing eigenvalue tail. Its finite arrowhead estimate $`2^r/3`$ is sufficient. The manuscript's sharper limiting ratio $`2^r`$, entrywise-positive and correlation-matrix extensions, LU results, and oversampling are not additional formal claims here.

Formalization and verification: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains original mathematical authorship. Chen, Epperly, Tropp and Webber retain credit for RPCholesky and its comparison problem. Substantial OpenAI Codex assistance, two complete nonauthor proof-source reviews and a separate runtime evidence audit are disclosed. No external human peer review or official Tau Ceti endorsement is claimed.

The project pins Lean 4.33.1, [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and [LeanCert](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926). The kernel-mode certificate $`\exp(1)\le3`$ is consumed by the denominator bound, actual-tail estimate and final contradiction; all rank and history calculations remain symbolic. All 27 exports use only `propext`, `Classical.choice` and `Quot.sound`. Run `lake build` in `randomized-and-low-rank-approximation/RA-02/lean`; [project instructions](lean/README.md) give the full Linux checks. Local macOS development and GitHub Linux verification are distinct. Later publication-commit and upstream PR checks remain separate from this immutable proof run.

[Formalization note](solution.tex) records the exact scope and attribution. Its PDF and the updated canonical PDF are rendered and inspected during publication; the historical literature-audit dates below are unchanged.

## Context and notation

For a Hermitian positive-semidefinite $`A\in\mathbb C^{n\times n}`$, define
the exact-arithmetic RPCholesky residuals by $`R_0=A`$. Conditional on
$`R_t\ne0`$, select $`j`$ with probability $`(R_t)_{jj}/\mathop{\mathrm{tr}}\nolimits(R_t)`$
and set

```math
R_{t+1}=R_t-\frac{R_t(:,j)R_t(j,:)}{(R_t)_{jj}}.
```

If $`R_t=0`$, keep all subsequent residuals zero. Eigenvalues are ordered
$`\lambda_1(A)\geq\cdots\geq\lambda_n(A)\geq0`$, and
$`\tau_r(A)=\sum_{j>r}\lambda_j(A)`$. This is the pivot rule in Chen,
Epperly, Tropp, and Webber, [*Randomly pivoted Cholesky: Practical
approximation of a kernel matrix with few entry evaluations*](https://doi.org/10.1002/cpa.22234),
Algorithm 1; their Lemma 5.5 gives the current comparison
$`\mathbb E\mathop{\mathrm{tr}}\nolimits(R_r)\leq2^r\tau_r(A)`$.

## Problem statement

Do constants $`C>0`$ and $`p\geq0`$ exist such that, for every $`n\geq1`$,
every Hermitian positive-semidefinite $`A\in\mathbb C^{n\times n}`$, and
every integer $`1\leq r\leq n`$,

```math
\mathbb E\mathop{\mathrm{tr}}\nolimits(R_r)\leq Cr^p\tau_r(A)?
```

Both constants must be independent of $`n,r,A`$. Exactly $`r`$ RPCholesky
steps are permitted, with the zero-residual convention above. This asks
for a polynomial approximation factor without oversampling; [RA-01](../RA-01/README.md) instead
allows additional pivots to obtain relative error near one.

## References

Epperly, [*Make the Most of What You Have*](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf),
§11.1, Conjecture 11.2, p. 182; Chen et al.,
[RPCholesky](https://doi.org/10.1002/cpa.22234), Lemma 5.5, p. 1020.
Gilles and Wilber, [*Low-Rank Approximation by Randomly Pivoted LU*](https://arxiv.org/html/2601.22344v1),
§3.1, paragraph following Theorem 3, explicitly reiterate this conjecture.

## Source normalization

The dissertation calls $`A^{(r)}`$ a residual but
prints $`\mathop{\mathrm{tr}}\nolimits(A-A^{(r)})`$, without expectation. We use its
cited Lemma 5.5 to correct both notation defects. The later paper confirms
the intended polynomial improvement over that lemma's $`2^r`$ factor.

## Status check

Searches for `RPCholesky r-step polynomial`,
`RPCholesky conjecture polynomial`, and the cited papers found no resolution.
Epperly's August 2026 oversampling theorem does not supply a polynomial
factor at exactly $`r`$ steps. Its Theorem 1.2 is noninformative at $`k=r`$.

## Audit — 2026-09-10

Rechecked [Gilles–Wilber's discussion after Theorem 3](https://arxiv.org/html/2601.22344v1), which reiterates the polynomial-factor conjecture. Exactly-$`r`$-step and later RPCholesky searches found no resolution. The [August oversampling theorem](https://arxiv.org/html/2608.20633v1) does not establish the displayed factor after exactly $`r`$ pivots.

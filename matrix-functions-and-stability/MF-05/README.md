# MF-05 — Local Hölder continuity of the joint spectral radius

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because reducible families obstruct uniform perturbation estimates; community impact comes from conditioning and robustness of stability computations.  
**Status:** Lean verified  
**Last checked:** 2026-09-17  

<!-- colbrook-jsr-growth -->
## Resolution — 2026-09-11

**Affirmative resolution.** Matthew J. Colbrook's [complete manuscript, Theorem 2 and Corollary 7](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/uniform_growth_and_holder.pdf) proves the stronger uniform estimate

```math
|\widehat\rho(\mathcal M)-\widehat\rho(\mathcal N)|
\le d(2d+1)L^{1-1/d}d_H(\mathcal M,\mathcal N)^{1/d}
```

for any two nonempty compact real or complex matrix families in the spectral-norm ball of radius $`L>0`$. Choosing a common norm ball around a fixed family gives the exact local two-family assertion below, including reducible families and zero joint spectral radius. For $`d=1`$ the Lipschitz constant is one. The exponent $`1/d`$ is sharp in general; no Lipschitz lower-bound resolution of MF-06 is asserted.

The complete original proof passed [independent Codex-agent review](../../references/colbrook-jsr-growth-2026-09-11/verification/reviews/MF-05-MF-07-review.md). [Authored TeX](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/uniform_growth_and_holder.tex) · [Submission, authorship and verification record](../../references/colbrook-jsr-growth-2026-09-11/README.md). The proof was developed with AI assistance. The 11 September audit was informal; the subsequent Lean verification is recorded below. No external human peer review is claimed. The original statement and prior evidence below are retained, and the ratings above are historical. This entry no longer contributes to the open count.

<!-- /colbrook-jsr-growth -->

## Lean proof and verification evidence

**The complete original target is Lean verified, 17 September 2026.** The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/06b8cf49740205c4b7b0b71ee5c636855fbe26a6/matrix-functions-and-stability/MF-05/lean/Solution.lean) at revision `06b8cf49740205c4b7b0b71ee5c636855fbe26a6` passed [non-root Linux run 35252365986](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35252365986/job/105307710518). The [retained execution evidence](lean/verification/linux-2026-09-17/README.md) authenticates all 193 submitted project inputs and 14 exported statements. Comparator statement matching, default-kernel replay, standard transitive axioms, sandbox checks and rejection controls all passed.

The main declaration `NLA.MF05.canonical_local_holder` chooses positive radius and constant before both compact complex matrix families vary. It covers every positive dimension, infinite generating families, reducibility, zero joint spectral radius and zero Hausdorff distance. `NLA.MF05.spectral_hausdorff_semantics` identifies the literal maximum-of-suprema-of-infima metric, and `NLA.MF05.general_root_limit_semantics` proves the full chronological-product root-limit meaning of the radius, including radius zero. `NLA.MF05.uniform_holder_estimate` proves the displayed uniform bound. The [14 exact contracts](lean/Challenge.lean) and [source correspondence](lean/SourceCorrespondence.md) record the comparison with the unchanged original target. Sharpness examples and the better scalar Lipschitz constant are not additional formal claims.

Formalization and verification submission: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains mathematical proof credit. Two independent statement reviews preceded implementation; two independent nonauthor final source reviews approved the complete proof. [Review records](lean/reviews/README.md) disclose substantial OpenAI Codex assistance and the reviewers' exact scopes.

The project pins Lean 4.33.1, [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and [LeanCert](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926). The consumed LeanCert certificate proves $`0<1/2<1`$ in kernel mode; the remaining argument is symbolic. Every export has only `propext`, `Classical.choice` and `Quot.sound` as transitive axioms. Run `lake build` in `matrix-functions-and-stability/MF-05/lean`; [full reproduction instructions](lean/README.md) distinguish the actual local builds from the final Linux check.

## Context and notation

Let $`\mathcal H_d`$ denote the nonempty compact subsets of
$`\mathbb C^{d\times d}`$. Use the spectral norm and its Hausdorff distance

```math
d_H(\mathcal M,\mathcal N)=\max\left\{
\sup_{A\in\mathcal M}\inf_{B\in\mathcal N}\|A-B\|_2,
\sup_{B\in\mathcal N}\inf_{A\in\mathcal M}\|A-B\|_2\right\}.
```

The joint spectral radius is

```math
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
```

These definitions also apply to finite real matrix sets. The ordinary spectral
radius of one matrix is written $`\rho(A)`$.

## Problem statement

For every $`d\ge1`$ and $`\mathcal M_0\in\mathcal H_d`$, do
there exist $`r,C>0`$ such that

```math
|\widehat\rho(\mathcal M)-\widehat\rho(\mathcal N)|
\le C d_H(\mathcal M,\mathcal N)^{1/d}
```

whenever $`d_H(\mathcal M,\mathcal M_0)< r`$ and
$`d_H(\mathcal N,\mathcal M_0)< r`$?

## Reference and status evidence

Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
Linear Algebra Appl. 704 (2025), 92–122,
[DOI](https://doi.org/10.1016/j.laa.2024.09.016), §2, Conjecture 3 (L1).
Pointwise results in that paper do not prove this local assertion.

## Additional status evidence

Searches combining “joint spectral
radius” with “local Hölder”, “Lipschitz lower”, “trajectory bounds”, the authors'
names, and 2025/2026 found no later resolution. These searches supplement the
explicit 2025 conjectures; they do not establish exhaustiveness. The three entries
are separately named assertions in the source, not a count of dimensional cases.

## Audit — 2026-09-10

Rechecked [Epperlein–Wirth, §1 and Conjecture 3 (L1)](https://arxiv.org/html/2311.18633v2). Local Lipschitz continuity settles the irreducible-family subcase, but the displayed exponent for arbitrary compact families remains open. Author and local-Hölder follow-up searches found no resolution; the weaker general pointwise results do not suffice.

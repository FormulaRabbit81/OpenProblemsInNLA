# MF-07 — Uniform polynomial bounds for products at joint spectral radius one

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because the constant must be uniform over all families of a given dimension; community impact spans transient growth and stability analysis.  
**Status:** Lean verified  
**Last checked:** 2026-09-17  

## Lean proof and verification evidence

**The complete original target is Lean verified, 2026-09-17 (UTC).** The [immutable proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/b2b9acc83ad7d6b7d3888de8390475a30c720af8/matrix-functions-and-stability/MF-07/lean/Solution.lean) at revision `b2b9acc83ad7` passed [non-root Linux run 35172783207](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35172783207/job/105047879291). The [retained source-bound evidence](lean/verification/linux-35172783207/README.md) and [independent runtime review](lean/reviews/canonical-runtime/REVIEW.md) cover all 297 submitted inputs, all 18 exported statements, default-kernel replay, Comparator, standard transitive axioms and actual rejection/isolation controls.

`NLA.MF07.canonical_uniform_bound` chooses a positive constant for each dimension before quantifying over every nonempty compact complex matrix family, every positive product length and every switching word. `NLA.MF07.radius_one_semantics` proves the correspondence with the original nth-root joint-spectral-radius limit. Matrix products and norms are the actual chronological products and Euclidean operator norms. Infinite compact families, reducibility, repetitions and dimension one are included. The [definitions and 18 independent contracts](lean/Challenge.lean) and [source correspondence](lean/SourceCorrespondence.md) record the full match.

The formal proof uses the sufficient dimension-only constants

```math
\Theta_1=1,\qquad
\Theta_d=d\left(\frac{6d^2}{d-1}\right)^{d-1}\quad(d\ge2).
```

This settles the original existential bound. The manuscript's smaller constant, sharpness, general-radius formula, bounded/real-family extensions and separate MF-05 theorem are outside this formal claim. Its mathematical resolution remains unchanged below.

Formalization and verification submission: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains original mathematical proof credit. Epperlein and Wirth retain credit for the question. Substantial OpenAI Codex assistance and scoped independent AI-agent reviews are disclosed; no official Tau Ceti endorsement, human peer review or new priority claim is made.

The project pins Lean 4.33.1, [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and [LeanCert](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926). Its consumed LeanCert certificate proves $`\exp(1)\le3`$ in kernel mode without interval subdivision. All 18 exports use only `propext`, `Classical.choice` and `Quot.sound`. Run `lake build` in `matrix-functions-and-stability/MF-07/lean`; [project instructions](lean/README.md) give the complete Linux check. The local macOS development run and the actual GitHub check are distinct. Later publication-commit and upstream PR executions remain separate from this immutable proof run.

The [formalization note](solution.pdf) and its [LaTeX source](solution.tex) record the scope and authorship.

<!-- colbrook-jsr-growth -->
## Resolution — 2026-09-11

**Affirmative resolution.** Matthew J. Colbrook's [complete manuscript, Theorem 1 and Proposition 5](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/uniform_growth_and_holder.pdf) proves the displayed bound for every dimension and every nonempty compact complex matrix family of joint spectral radius one, with

```math
\Theta_1=1,\qquad
\Theta_d=d\left(\frac{2ed^2}{d-1}\right)^{d-1}\quad(d\ge2).
```

This constant is independent of the family and its cardinality. The proof covers every switching word and every positive length, without irreducibility or an exact extremal norm. The growth exponent $`d-1`$ is sharp in general; the displayed constant is not asserted optimal. The result also holds for nonempty bounded real or complex families.

The complete original proof passed [independent Codex-agent review](../../references/colbrook-jsr-growth-2026-09-11/verification/reviews/MF-05-MF-07-review.md). [Authored TeX](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/uniform_growth_and_holder.tex) · [Submission, authorship and verification record](../../references/colbrook-jsr-growth-2026-09-11/README.md). The proof was developed with AI assistance; no external human peer review or formal verification is claimed. The original statement and prior evidence below are retained, and the ratings above are historical. This entry no longer contributes to the open count.

<!-- /colbrook-jsr-growth -->

## Context and notation

Let $`\mathcal H_d`$ denote the nonempty compact subsets of
$`\mathbb C^{d\times d}`$.

The joint spectral radius of a nonempty compact set $`\mathcal M\subset\mathbb C^{d\times d}`$ is

```math
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
```

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $`\rho(A)`$.

## Problem statement

Does each $`d\ge1`$ admit $`\Theta_d>0`$ such that every
$`\mathcal M\in\mathcal H_d`$ with $`\widehat\rho(\mathcal M)=1`$ satisfies

```math
\|A_k\cdots A_1\|_2\le\Theta_d(Lk)^{d-1},\qquad
L=\max_{A\in\mathcal M}\|A\|_2,
```

for all $`k\ge1`$ and all $`A_1,\ldots,A_k\in\mathcal M`$?

## Reference and status evidence

Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
§2, Conjecture 3 (L3). Lemma 27 proves dimension two. The constant above must
be independent of the family.

## Common follow-up screen for [MF-05](../MF-05/README.md)–MF-07

Searches combining “joint spectral
radius” with “local Hölder”, “Lipschitz lower”, “trajectory bounds”, the authors'
names, and 2025/2026 found no later resolution. These searches supplement the
explicit 2025 conjectures; they do not establish exhaustiveness. The three entries
are separately named assertions in the source, not a count of dimensional cases.

## Audit — 2026-09-10

Rechecked [Conjecture 3 (L3) and Lemma 27](https://arxiv.org/html/2311.18633v2): dimension two is proved, but higher-dimensional uniform constants remain conjectural. Searches for trajectory bounds and subsequent Epperlein–Wirth work found no resolution. Family-dependent polynomial estimates do not establish the displayed uniform statement.

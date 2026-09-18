# MF-14 — Degree coverage with seven matrix multiplications

**Difficulty:** challenging

**Importance:** interesting to the community

**Rating rationale:** Historical ratings for the original conjecture: challenging because numerical evidence for coefficient-space coverage needs exact algebraic justification; community impact comes from multiplication budgets for practical matrix-function evaluation.

**Last checked:** 2026-09-17

**Status:** Solved


## Resolution — exact maximum 47, 17 September 2026

**Author:** Marcus Webb, The University of Manchester. Developed with substantial ChatGPT/Codex assistance. Separate Codex agents reviewed the mathematics, and an independently implemented exact verifier reconstructed the full polynomial and its derivatives. This is informal AI-agent review, not external human peer review or formal verification.

[Theorem 1 of the complete proof](../../references/webb-mf14-degree47-2026-09-17/proof.pdf) determines the exact maximum in the retained question:

```math
d_7=47.
```

Every complex polynomial of degree at most 47 belongs to the Zariski closure of seven-product outputs in the full coefficient space through degree 128. An explicit seven-product family has a rigorously certified order-47 contact with an invertible 48-by-48 coefficient Jacobian. Exact Gaussian-rational contraction bounds prove the contact exists; the inverse function theorem and a weighted input/output limit give the universal coverage statement, with every higher coefficient tending to zero.

A self-contained available-space dimension count gives $`\dim\overline{\mathcal P_7}^{\,Z}\le49`$. Irreducibility and the seven-product polynomial $`x^{128}`$ then exclude coverage of the entire degree-at-most-48 space. The new proof does not depend on the earlier border construction or on an external dimension theorem. Exact representation of every degree-47 polynomial and numerically stable coefficient recovery are not asserted.

[Standalone proof source](../../references/webb-mf14-degree47-2026-09-17/proof.tex) · [Exact certificates and reproduction](../../references/webb-mf14-degree47-2026-09-17/README.md) · [Independent review](../../references/webb-mf14-degree47-2026-09-17/verification/packaging-review.md). The original equality $`d_7=42`$, permanent ID and canonical path remain unchanged. The earlier degree-42 and degree-44 results below retain their attribution and archived evidence.

## Earlier negative resolution — degree 44, 17 September 2026

**Author:** Marcus Webb, The University of Manchester. Developed with substantial ChatGPT assistance; two separate Codex agents independently reviewed the proof and recomputed its exact certificates. This is informal AI-agent review, not external human peer review or formal verification.

The conjectured equality is false. [Theorem 1 of the complete proof](../../references/webb-mf14-degree44-2026-09-17/proof.pdf) establishes

```math
\mathbb C[x]_{\le44}\subseteq\overline{\mathcal P_7}^{\,Z}.
```

The construction first retains a suitable quadruple of polynomials in the joint closure of four-product computations (Lemma 2). Three more products give a 45-parameter coefficient map whose exact Jacobian determinant is 256. The argument uses the original complex field and all coefficients through degree 128; high-degree coefficients vanish in the limit rather than being discarded.

Corollary 3, using Jarlebring–Lorentzon's dimension theorem, gives $`44\le d_7\le47`$ for the maximum in the retained question. That contribution left the exact maximum undetermined while giving a complete negative answer to the specific equality $`d_7=42`$; the new theorem above now determines it as 47. No exact representation of every degree-44 polynomial, real Euclidean density, or numerical stability is asserted.

[Proof source](../../references/webb-mf14-degree44-2026-09-17/proof.tex) · [Independent reviews and reproduction](../../references/webb-mf14-degree44-2026-09-17/README.md) · [Source conversation and attribution](../../references/webb-mf14-degree44-2026-09-17/README.md#source-and-attribution). The permanent ID, canonical path and original mathematical target are retained. The degree-42 result below retains its separate credit.

<!-- colbrook-matrix-functions -->
## Verified partial result — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the stated partial results.**

A fixed seven-product scheme has a full-rank complex coefficient map, certified by a nonzero exact integer Jacobian minor. Its image contains a nonempty Zariski-open subset of $`\mathbb C[x]_{\le42}`$ and is Euclidean dense there.

This earlier result did not prove an upper bound excluding degree 43 and above, so at the time it left the maximal-degree equality open. It asserted neither exact representation of every polynomial nor real Euclidean dense coverage. The later degree-44 construction above now refutes that equality; the degree-42 theorem remains valid.

**Primary reference:** [complete authored PDF](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-14.pdf), [standalone TeX](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-14.tex), **Theorem 1 and equations (1)-(2)**. [Independent proof review](../../references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-14-review.md) · [Authorship and submission record](../../references/colbrook-matrix-functions-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-matrix-functions -->

## Problem statement

Start with the scalar polynomials $`1,x\in\mathbb C[x]`$. Allow arbitrarily many complex linear combinations of already computed polynomials and at most seven multiplications of two already computed polynomials. Let $`\mathcal P_7\subseteq\mathbb C[x]_{\le128}`$ be the set of possible outputs.

Identify a polynomial with its coefficient vector in $`\mathbb C^{129}`$ and let $`\overline{\mathcal P_7}^{\,Z}`$ be its Zariski closure: the common zero set of all polynomial equations in the coefficients that vanish throughout $`\mathcal P_7`$. Is

```math
\max\{d\in\{0,\ldots,128\}:\mathbb C[x]_{\le d}\subseteq\overline{\mathcal P_7}^{\,Z}\}=42?
```

The target concerns closure and the complex coefficient field. Exact representability of every polynomial is a stronger assertion.

## Why it matters

For a dense input matrix, matrix products dominate the cost of polynomial evaluation. The conjecture determines how much polynomial degree a budget of seven products can cover, providing a theoretical benchmark for matrix-function evaluation schemes.

## References

1. E. Jarlebring and G. Lorentzon, *The polynomial set associated with a fixed number of matrix-matrix multiplications*, arXiv:2504.01500v3 (13 August 2025), §2.2 (closure convention), §5.4, Conjecture 13. [Primary text](https://arxiv.org/html/2504.01500).
2. J. Sastre, J. Ibáñez, J. M. Alonso, and E. Defez, *Beyond Paterson–Stockmeyer: Advancing matrix polynomial computation*, WSEAS Transactions on Mathematics 24 (2025), 684–693, §4 (a five-product construction). [Primary paper](https://wseas.com/journals/mathematics/2025/b385106-036%282025%29.pdf), [DOI](https://doi.org/10.37394/23206.2025.24.68).
3. J. M. Alonso, J. Sastre, J. Ibáñez, and E. Defez, *A systematic framework for stable and cost-efficient matrix polynomial evaluation*, arXiv:2603.23143v1 (24 March 2026), abstract and conclusions. [Primary text](https://arxiv.org/html/2603.23143).

## Status check — 2026-09-08

The latest arXiv source remains v3 and labels the displayed equality a conjecture supported by computations. The later papers give constructions and stability procedures without establishing the seven-product degree-coverage claim. Searches included the exact title with `2026`, `Jarlebring Lorentzon conjecture seven multiplications 42`, and `Sastre polynomial evaluation 2026`. No resolution was located. A [3 September 2026 author talk](https://indico3.mpi-magdeburg.mpg.de/event/58/contributions/1074/) also describes higher-cost degree coverage as conjectural. Six-product real/complex formulations have a separate source ambiguity and are deliberately not included here.

## Audit — 2026-09-10

Rechecked [Conjecture 13 and Remark 14](https://arxiv.org/html/2504.01500): complex closure coverage at seven products is still conjectural, with concrete matrix-exponential applications. Title and seven-product searches found no exact proof. The [June 2026 degree-eight construction](https://arxiv.org/html/2606.24701v1) solves a different budget/degree problem.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

# MF-02 — Multiplication overhead of cubic sign compositions

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because optimal cubic compositions must be compared with unrestricted evaluation programs; community impact comes from reusable matrix-sign iterations.  
**Status:** Lean verified  
**Last checked:** 2026-09-15  

## Resolution - uniform constant-factor asymptotic order

**Resolution recorded 2026-09-12.** The canonical asymptotic-order target is settled:

```math
T_{\min}(m,\delta)=\Theta(m+1)\qquad(0<\delta<1),
```

with absolute constants uniform in the gap, including gaps depending on the multiplication budget. The [Theorem in Section 1 and proof in Sections 2-5](solution.md) give the explicit bounds

```math
\left\lfloor\frac m2\right\rfloor\le T_{\min}(m,\delta)\le m\quad(m\ge2),
\qquad T_{\min}(0,\delta)=T_{\min}(1,\delta)=1.
```

**Expository proof-note author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

**Prior work and exact scope.** Cheon, Kim and Kim's [ASIACRYPT 2020 work](https://doi.org/10.1007/978-3-030-64834-3_8), especially Lemma 3 and its constant-factor complexity analysis, already yields uniform constant-factor order by combination with the classical degree bound. The optimized cubic is the earlier [Chen-Chow construction, equations (3.3)-(3.6)](https://www.mcs.anl.gov/papers/P5059-0114.pdf), also discussed in [Polar Express, Appendix F](https://arxiv.org/html/2505.16932v5). The present self-contained note supplies the explicit comparison $`T_{\min}\le m`$; it claims neither a new cubic iteration nor first discovery of constant-factor optimality. The exact smallest stage count, the optimal leading constant, and the stronger source question comparing the errors at the same multiplication budget remain unanswered.

**Verification.** A separate [independent Codex-agent mathematical and scope review](../../references/stepaniants-mf02-2026-09-12/verification/independent-review/MF-02-independent-review.md) returned PASS for the theorem and the literal canonical asymptotic-order target. A second [independent source and attribution review](../../references/stepaniants-mf02-2026-09-12/verification/source-review/REVIEW.md) confirms the scope and prior-work distinctions. The [submission record](../../references/stepaniants-mf02-2026-09-12/README.md) preserves both reviews, the original candidate and exact checks. Substantial AI assistance is disclosed. Those original reviews were informal automated-agent reviews; the separate Lean verification is documented below. No external human peer review, novelty or priority certification is asserted.

The original target, permanent ID, references and dated history remain below. The displayed ratings are retained as historical ratings of that target.

## Lean proof and verification evidence

The complete canonical asymptotic-order result has a [Lean proof at immutable revision b873ead8](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/b873ead85b3c71cdba017a915d5ef6e73b1711ae/matrix-functions-and-stability/MF-02/lean/Solution.lean). The package pins Lean **4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

In namespace `NLA.MF02`, the main declarations are:

- `stage_minimum_attained`: the stage minimum is finite and attained.
- `stage_minimum_small_budgets`: both small-budget values equal one.
- `stage_minimum_bounds`: the displayed explicit bounds for every budget.
- `uniform_asymptotic_order`: uniform constant-factor order.

The nine supporting declarations are listed with their proofs and roles in [the manifest](lean/formalization.yaml):

- `uniform_error_is_maximum`
- `program_degree_bound`
- `cubic_degree_and_cost`
- `degree_error_lower_bound`
- `optimized_cubic_interval`
- `optimized_cubic_ratio`
- `cubic_error_bounds`
- `cubic_error_strictly_decreases`
- `unrestricted_error_small_budgets`

All thirteen are compared with independently reviewed [Challenge statements](lean/Challenge.lean).

The definitions retain arbitrary real gaps, every multiplication budget, free real linear combinations, stored-product reuse, the actual maximum error on both closed intervals and true coefficient infima. No coefficient optimizer is assumed. The [source correspondence](lean/SourceCorrespondence.md) explains the exact connection to the original target. The precise optimum beyond the two small budgets and the stronger same-budget comparison remain outside the resolved target.

On **15 September 2026**, GitHub's non-root Linux runner [verified this exact proof commit](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35016473743/job/104541199904) using the repository's shared pinned checker. The actual thirteen Solution exports passed LeanCert kernel assertions, Comparator statement/definition matching and a separate default-kernel replay. Every transitive axiom report contains only `propext`, `Classical.choice` and `Quot.sound`; no proof hole or native-execution axiom supports a target. The [retained raw evidence](lean/verification/linux-2026-09-15) includes source hashes and successful controls rejecting invalid proofs, mismatched statements and forbidden axioms. These checks ran on GitHub Linux; no local macOS Lean run is claimed.

Two independent AI-agent referees accepted the complete mathematical source and inspected those actual logs: [referee 1](lean/reviews/final/referee-elimination.md) and [referee 2](lean/reviews/final/referee-inequalities.md). They applied the repository's scoped Tau Ceti review protocol. This is distinct from external human peer review or certification of the checker software.

To build the proof yourself, open [the Lean project directory](lean/README.md) and run with Lean installed:

```
lake exe cache get && lake build +Solution
```

For the additional sandboxed Comparator, replay and rejection checks, follow the [Linux verification commands](../../docs/lean/README.md). The Challenge's deliberate placeholders belong to the independent contract environment and are never imported by Solution. Mathematical attribution above remains unchanged.

## Context and notation

For $`m\in\mathbb N_0`$ and $`0<\delta<1`$, put

```math
I_\delta=[-1,-\delta]\cup[\delta,1].
```

Let $`\mathcal P_m`$ consist of real polynomials computed from $`1,x`$ by
straight-line programs using at most $`m`$ nonscalar multiplications; real linear
combinations cost nothing. Define

```math
E_m(\delta)=\inf_{p\in\mathcal P_m}
\max_{x\in I_\delta}|p(x)-\mathop{\mathrm{sign}}\nolimits(x)|.
```

The arithmetic model concerns a single polynomial identity valid for matrices of every size.

## Problem statement

Define

```math
C_T(\delta)=\inf_{a_t,b_t\in\mathbb R}
\max_{x\in I_\delta}|(q_T\circ\cdots\circ q_1)(x)-\mathop{\mathrm{sign}}\nolimits(x)|,
\qquad q_t(x)=a_tx+b_tx^3.
```

Determine the asymptotic dependence on $`m,\delta`$ of

```math
T_{\min}(m,\delta)=\inf\{T\in\mathbb N_0:C_T(\delta)\le E_m(\delta)\},
```

where the empty composition is $`x`$ and $`\inf\varnothing=+\infty`$.
Each stage costs at most two matrix products.

## References and status evidence

Amsel et al.,
[Simons workshop report](https://arxiv.org/html/2602.05394v3), §6.3, Problem 6.5.
Rubensson, Jarlebring and Lorentzon,
[degree-eight recursive expansion](https://arxiv.org/html/2606.24701v1), §7,
provides a June 2026 follow-up discussion; it does not settle this comparison.

## Scope

[MF-01](../MF-01/README.md) asks for an optimum value over general evaluation programs.
This problem measures the price of a particular, reusable composition architecture;
the two tasks are related but have different requested outputs.

## Audit — 2026-09-10

Rechecked [Problem 6.5](https://arxiv.org/html/2602.05394v3#S6.SS3) and the [degree-eight paper's concluding discussion](https://arxiv.org/html/2606.24701v1). The optimal composition comparison remains posed. Searches for cubic and recursive sign-expansion improvements found no resolution of this exact multiplication-overhead target.

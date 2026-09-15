# SP-04: generic failure of the smallest-absolute-multiplier rule

**Stage: mathematical statement preparation.** Definitions and eleven proposed
Challenge signatures type-check. The Challenge contains eleven intentional
placeholders and proves nothing. Solution imports definitions only; there is no
proof implementation. Independent exact-byte statement approvals, complete
proofs, final source reviews and isolated Linux verification are all pending.
The canonical problem remains **Solved**.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical resolution:** Matthew J. Colbrook, Department
of Applied Mathematics and Theoretical Physics, University of Cambridge.
The [canonical statement](../README.md) and [complete original proof](../solution.md)
are preserved unchanged, including their historical attribution.

## Full intended target

The question concerns all real matrices with determinant either +1 or -1 and
all true stationary pairs satisfying `Xᵀ(U-X)=cI`. It asks whether the pair with
smallest absolute multiplier gives the nearest matrix in the actual Frobenius
norm, outside a proper real algebraic exception and in every dimension at least
two. The proposed result defeats every possible nonzero polynomial exception
in dimension three. Each counterexample must have an invertible data matrix,
distinct squared singular values, a finite full stationary set, a unique
least-absolute pair, and a strictly better feasible matrix.

The [dossier](NUMERICAL_TARGETS.md) retains the complete source family and records
the exact numerical and semantic obligations. The open family is described by
opposite signs of the Gram characteristic polynomial at three disjoint pairs
of rational endpoints. It lies in the full nine-dimensional matrix space.
All norm comparisons use an explicit square root of the sum of entry squares.
Neither a default matrix norm nor a diagonal-only genericity claim is used.

The definitions are literal mathematical objects, and
[comparator.json](comparator.json) permits no definition holes. The final proof
must consume explicit LeanCert kernel-mode certificates and permit only
`propext`, `Classical.choice`, and `Quot.sound`. A truthful completed-project
`formalization.yaml` will be added with the implemented proofs.

## Reproduction of the statement boundary

```bash
lake exe cache get
lake build Challenge
```

This checks types only. The deliberate specification holes cannot support a
verification claim. The shared [review protocol](../../../docs/lean/REVIEW.md)
requires two independent non-implementing agents to approve exact mathematical
and numerical statements before proof implementation. Later stages separately
require full-source review and the pinned [Linux harness](../../../tools/lean/HARNESS.md),
including actual Lean4 Comparator, default-kernel replay and rejection controls.

The pinned [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
and [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
projects supply structure/API references. Reviews follow the repository's Tau
Ceti adaptation and are disclosed as AI-agent reviews, without claiming
external human review or official endorsement.

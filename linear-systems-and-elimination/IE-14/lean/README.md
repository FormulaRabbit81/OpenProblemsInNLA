# IE-14: sharp growth for complex cyclic tridiagonal partial pivoting

**Stage: approved pre-proof boundary.** Definitions and seven Challenge specifications
type-check. Their intentional placeholders establish no theorem; Solution imports
only definitions. Both independent exact-byte statement reviews approve the complete boundary.
The [statement freeze](reviews/statement-freeze.json) records the ten approved inputs;
no proof implementation is included in this boundary commit. Canonical status remains **Solved**.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical resolution:** Matthew J. Colbrook, Department
of Applied Mathematics and Theoretical Physics, University of Cambridge.
The [complete original target](../README.md), original manuscript and attribution
remain preserved.

## Complete proposed scope

For every n≥4, the sharp growth factor for nonsingular complex cyclic tridiagonal
matrices with both corners nonzero is `Nat.fib (n+1) + 1`. Every maximal-modulus
partial-pivoting tie choice and every entry of every active Schur complement is
included. Column order is fixed. Actual row swaps begin at the original input;
there is no preliminary reordering.

The finite maxima use literal complex entry moduli. The public boundary includes
existence of complete admissible paths for every nonsingular input, the universal
all-active-entry bound, and a rational all-size witness with initial maximum one.
The witness follows the explicit path that keeps the first row, then selects the
current last row at every later stage. `IsGreatest` supplies actual attainment and
nonemptiness before the real-supremum equality is stated.

The exact half coefficient in the witness requires a consumed LeanCert kernel
certificate for `0 < (1/2 : ℝ)` and `1/2 ≤ 1`. This certificate supports nonzero
pivots and input-entry bounds. Universal complex front bounds and Fibonacci
induction remain symbolic proof obligations.

The complete [mathematical and numerical dossier](NUMERICAL_TARGETS.md) includes
exact source hashes, all seven targets, the original-label front invariant and
the literal witness trajectory. [Independent statement referee 1](reviews/statement-referee-1.md)
and [referee 2](reviews/statement-referee-2.md) approved those exact inputs.

## Statement reproduction and review

```bash
lake exe cache get
lake build Challenge
```

The default target is the frozen specification module. The eventual proof module
must not import Challenge. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted, and [comparator.json](comparator.json) permits no definition holes.

The [repository review protocol](../../../docs/lean/REVIEW.md) adapts Tau Ceti
referee standards through two independent non-implementing AI reviewers at the
statement, complete-source and operational gates. Actual pinned Lean4 Comparator,
default-kernel replay, real sandbox probes and rejection controls must pass the
[Linux harness](../../../tools/lean/HARNESS.md) before any Lean verified promotion.

The pinned [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
and [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
projects supply structure/API references. Local IE-05/IE-15 definitions inform
elimination and finite-maximum conventions; their real or rook-pivoting theorems
are not assumed to cover this complex GEPP target. No external human review or
official endorsement is claimed.

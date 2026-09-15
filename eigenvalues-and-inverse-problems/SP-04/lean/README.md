# SP-04: generic failure of the smallest-absolute-multiplier rule

**Stage: complete local proof; independent final review and authoritative Linux
verification pending.** All eleven reviewed declarations compile with explicit
kernel-trust assertions and only `propext`, `Classical.choice`, and `Quot.sound`.
The ten pre-proof statement/dependency inputs remain unchanged from the two
independent approvals at boundary commit `623e14e6`. The canonical problem remains
**Solved** until full-source review, actual Comparator correspondence, isolated
Linux verification and operational review pass. No completed Linux verification
or final referee approval is claimed at this stage.

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
two. The implemented result defeats every possible nonzero polynomial exception
in dimension three. Each counterexample has an invertible data matrix,
distinct squared singular values, a finite full stationary set, a unique
least-absolute pair, and a strictly better feasible matrix.

The [dossier](NUMERICAL_TARGETS.md) retains the complete source family and records
the exact numerical and semantic obligations. The open family is described by
opposite signs of the Gram characteristic polynomial at three disjoint pairs
of rational endpoints. It lies in the full nine-dimensional matrix space.
All norm comparisons use an explicit square root of the sum of entry squares.
Neither a default matrix norm nor a diagonal-only genericity claim is used.

The definitions are literal mathematical objects, and
[comparator.json](comparator.json) permits no definition holes. The proof
consumes four explicit LeanCert kernel-mode certificates and uses only
`propext`, `Classical.choice`, and `Quot.sound`. The current
[formalization.yaml](formalization.yaml) reports local completion and the remaining
independent and operational gates.

## Proof structure and computation

| Modules | Mathematical content |
| --- | --- |
| `Certificates`, `ScalarRoots`, `ScalarPositive`, `Scalar` | Four consumed kernel certificates; exact square-root identities; exclusion of all competing nonnegative multipliers; unique negative selection among every real quadratic-root pattern; strict distance improvement. |
| `MatrixStationary`, `Diagonal` | Reduction of every stationary matrix through Gram commutation, and the complete counterexample for every ordered real triple in the original box. |
| `Finiteness` | An unexpanded 8×8 companion-tensor eliminant vanishes for every stationary multiplier. A rank-one calculation at zero proves it is nonzero; finite polynomial roots and quadratic fibers prove finiteness of the entire stationary set. |
| `Orthogonal`, `Witness` | Both determinant signs, the literal Frobenius norm, all stationary pairs, unique selection and finiteness transport under the actual two-sided orthogonal action. |
| `SpectralIntervals`, `SVD`, `Spectrum` | Strict polynomial signs define a nonempty open set in all nine entries. Three real Gram roots give an ordered orthogonal eigenbasis; column normalization constructs an actual SVD and proves invertibility and simple spectrum. |
| `Generic`, `Proof` | Polynomial uniqueness on a box with infinite real sides defeats every proper algebraic exception, then negates the original rule across all dimensions. |

The proof uses no numerical approximation of the selected multiplier, derivative
bound, expanded eliminant, or singular-value continuity theorem. It proves the
entire original ordered scalar box and transports to every actual admissible SVD;
the explicit polynomial-sign open subset is sufficient to refute genericity.
The manuscript's illustrative decimals and optional asymptotic observations are
preserved without turning them into proof premises.

## Reproduction and review gates

```bash
lake exe cache get
lake build Challenge
lake build Solution
```

The default Lake target is deliberately the frozen Challenge. Its eleven
specification placeholders establish no mathematics; the separate Solution has
no proof holes. Local logs are in `verification/local-challenge-build.log` and
`verification/local-solution-build.log`. The latter prints the transitive axioms
of every exported result, and every result also asserts kernel trust.

The [review protocol](../../../docs/lean/REVIEW.md) requires two independent
non-implementing agents to approve exact mathematical and numerical statements
before implementation. Both approvals and their sealed inputs are retained in
`reviews/`. Complete-source reviews and the pinned
[Linux harness](../../../tools/lean/HARNESS.md) remain separate gates. The Linux
run must use actual Lean4 Comparator, default-kernel replay, the real sandbox,
and successful rejection controls; local compilation does not replace it.

The pinned [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
and [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
projects supply structure/API references. Reviews follow the repository's Tau
Ceti adaptation and are disclosed as AI-agent reviews, without claiming
external human review or official endorsement.

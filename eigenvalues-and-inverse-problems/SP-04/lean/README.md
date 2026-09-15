# SP-04: generic failure of the smallest-absolute-multiplier rule

**Verification status: Lean verified.** All eleven complete-target declarations
passed fresh isolated Linux Comparator, default-kernel replay and permitted-axiom
checks. Both independent complete-source reviews and both operational audits passed.
The ten pre-proof inputs remain unchanged from the two independent approvals
at boundary commit `623e14e6`.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical resolution:** Matthew J. Colbrook, Department
of Applied Mathematics and Theoretical Physics, University of Cambridge.
The [canonical statement](../README.md) and [complete original proof](../solution.md)
are preserved in full, including their historical attribution. The canonical page
adds only verification information and updates status/date.

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
`propext`, `Classical.choice`, and `Quot.sound`. The
[formalization.yaml](formalization.yaml) records complete verification, attribution,
all eleven exports and the reviewed evidence.

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
`reviews/`. Both complete-source reviews approved: [referee 1](reviews/final-referee-1.md)
and [referee 2](reviews/final-referee-2.md). The pinned
[Linux harness](../../../tools/lean/HARNESS.md) then ran actual Lean4 Comparator,
default-kernel replay, the real sandbox and successful rejection controls.

The pinned [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
and [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
projects supply structure/API references. Reviews follow the repository's Tau
Ceti adaptation and are disclosed as AI-agent reviews, without claiming
external human review or official endorsement.


## Authoritative Linux verification

[Run 35025876241, attempt 1](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35025876241/attempts/1) verified immutable proof revision
[`fcd722e9`](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/fcd722e923a339dfeee89051886e82c7384a04d7/eigenvalues-and-inverse-problems/SP-04/lean)
on Ubuntu 24.04. All eleven Challenge/Solution targets passed actual Comparator
correspondence, transitive permitted-axiom checks and default-kernel replay.
The target verification also passed real sandbox probes, three raw-kernel controls,
five Comparator regressions, and separate sorry/native rejection controls.

The [permanent archive](verification/linux-2026-09-15/) retains the original ZIP,
all thirteen extracted members, GitHub provenance and the full source receipt.
Artifact `10419254479` has SHA-256
`eae47bb19e2a64ffc99e383b204c8be89136cfe5755deb86f1e49981c9d1aa6a`.

```bash
cd verification/linux-2026-09-15
shasum -a 256 -c SHA256SUMS
```

Both independent operational audits approved: [referee 1](reviews/linux-referee-1.md)
and [referee 2](reviews/linux-referee-2.md). They checked all
88 candidate input hashes against the immutable verified Git revision
and approved source. The standalone checker-controls job was skipped because
shared tools were unchanged; all required controls ran within the actual SP-04
verify job.

Publication changes update status, documentation, evidence and rendered artifacts.
Mathematical statements, proofs and dependency inputs remain those verified at
the immutable proof revision. Historical pending-stage reports are closed by
the later approvals. No second independent Linux execution, external human review
or official Tau Ceti endorsement is claimed.

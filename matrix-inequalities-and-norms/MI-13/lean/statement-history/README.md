# MI-13: statement draft for the complete rectangular inequality

This is a private statement-only draft: Definitions and 36 deliberate Challenge
holes, with no proof implementation or successful Lean execution. The numerical
boundary and definition/contract plan were sealed in `NUMERICAL-FIRST.json`
before either active Lean file was written. Exact statements still require two
independent reviews and actual local elaboration before freezing.

The target is the original complex inequality, for every `m,n ≥ 2` and every
`A,C : Matrix (Fin m) (Fin n) ℂ`, `B : Matrix (Fin n) (Fin m) ℂ`:

```
‖ABC − CBA‖F² ≤ 2 ‖B‖op² (σ₁(A)² + σ₂(A)²) ‖C‖F².
```

The norms are the actual Euclidean Frobenius and continuous-linear-map operator
norms; singular values are Mathlib's actual decreasing Gram-spectrum sequence.
Zeros, deficient ranks, repeated singular values and both dimension orderings
are included. The final theorem has no SVD, invertibility or external
commutator-estimate premise.

Read [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md),
[DEFINITION-AND-CONTRACT-PLAN.md](DEFINITION-AND-CONTRACT-PLAN.md),
[Definitions](NLA/MI13/Definitions.lean), [Challenge](Challenge.lean), and
[SourceCorrespondence.md](SourceCorrespondence.md). The finite internal proof
route is retained as reference text in `sources/route/`. Its earlier feasibility
approval does not approve these new Lean statements automatically.

The planned proof uses a partially indexed orthonormal-basis extension for an
all-rank SVD, one Rayleigh maximum on the commutator space, a conjugate-linear
pair of orthogonal eigenvectors, and exact sum-index block padding. No matrix
enumeration, interval grid or full ordered commutator-space eigenbasis is
needed. The only planned LeanCert calculation is kernel-mode positivity of the
exact rational half, consumed in Frobenius averaging; it has not been run.

`comparator.json` proposes all 36 declarations and no definition holes.
`Solution.lean` does not exist. Metadata lists no proved results. The static
v0.4 schema check and text-level coverage check, if reported in `STATIC-CHECKS.json`,
are not Lean, Comparator, or the repository's completed-project validator.

Development follows the user's local-first workflow: the coordinator alone
runs one local Lean process with one thread and a 4096 MiB limit, then fixes
failures locally. Fresh non-root Linux default-kernel/Comparator/rejection and
sandbox checks are later publication gates. See [REVIEW-PLAN.md](REVIEW-PLAN.md).

Formalization contributor: **George Stepaniants**, Department of Computing and
Mathematical Sciences, California Institute of Technology. OpenAI Codex assisted
the draft. Nobori's original question, Audenaert's established refined
commutator theorem, and the repository's reduction retain their attribution;
this project proposes to prove the commutator theorem internally. No novelty,
external peer review, official Tau Ceti endorsement, verified count increment,
fresh duplicate search or publication is claimed. The historical canonical
source and bounded duplicate-audit scope are retained with exact identities.

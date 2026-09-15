# SP-05: a symmetric minimizer for the positive definite Jordan–Kronecker product

**Stage: pre-proof statement preparation.** The definitions and six proposed
Challenge declarations are specifications only. Challenge's six deliberate
placeholders prove nothing; Solution currently imports definitions only.
Independent exact-byte statement approvals, implementation, final source
reviews and actual isolated Linux verification are pending. The canonical
problem remains **Solved**.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical proof:** Matthew J. Colbrook, Department of
Applied Mathematics and Theoretical Physics, University of Cambridge.
The complete [canonical statement](../README.md) and [original proof](../solution.md)
remain unchanged. The original conjecture is credited to Nargiz Kalantarova
and Levent Tunçel.

## Exact intended scope

For every real symmetric positive definite pair in every dimension at least
two, compare the minimum of the actual `A ⊗ B` Rayleigh quotient on the `+1`
and `-1` eigenspaces of the commutation permutation matrix. The result must
prove attainment of both minima and the displayed inequality. All nonzero real
vectors in each sector are included; no rank, commutativity or simple-eigenvalue
assumption is introduced.

Column stacking is the existing `Matrix.vec`, indexed by `(column,row)`.
`commutationMatrix` is the literal permutation matrix; `sectorValues` is the
set of its nonzero vectors' quotient values. The stronger intermediate target
constructs a nonzero real positive-semidefinite eigenmatrix attaining the global
minimum of the Jordan–Kronecker sum. Its dimension is explicitly positive.
The explicit skew matrix has squared Frobenius norm two. The planned LeanCert
kernel certificate `0 < 2` must be consumed to establish its nonzero normalized
representative, needed to prove the skew minimum exists.

The [Comparator configuration](comparator.json) covers every proposed export and
allows no definition holes. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. No verified-project metadata or status promotion is appropriate
before implementation and the required mechanical gates.

## Statement reproduction and review

```bash
lake exe cache get
lake build Challenge
```

This checks statement types only. Two independent non-implementing reviewers
must approve the complete numerical/mathematical dossier and exact input bytes
before any proof implementation. The repository's
[review protocol](../../../docs/lean/REVIEW.md) adapts Tau Ceti standards and
requires separate final-source and operational reviews. Actual pinned Lean4
Comparator, default-kernel replay, the sandbox and rejection controls are
required by the [Linux harness](../../../tools/lean/HARNESS.md).

The pinned [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
and [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
projects are structure/API references. Reviews are disclosed as independent
AI-agent reviews, without an external-human-review or official-endorsement claim.

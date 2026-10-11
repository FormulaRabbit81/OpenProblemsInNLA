# RA-10 completed proof: review guide

The candidate proves the unchanged `NLA.Statements.RA10.Target` with universal
constant 11. It extends the existing RA-10 foundations at
`50106db1b75a1019b708f495db747ab37bb8efbd`.
Local Lean checking is complete; independent review and isolated non-root
Linux Comparator verification remain outstanding.

## Start here

- [Final theorem](../../../../lean-statements/NLA/Proofs/RA10/OperatorMonotoneRepresentation.lean):
  `NLA.Proofs.RA10.ra10_target`, via `transferBound_eleven` and the unconditional
  representing-measure theorem.
- [Completion checklist](COMPLETION_CHECKLIST.md): proof sections, reuse and
  the remaining verification gates.
- [Ridge transfer](SPECTRAL_TRANSFER_PROGRESS.md): compression, spectral
  perturbation and constant-11 assembly.
- [Operator-monotone representation](REPRESENTATION_PROGRESS.md): compactness,
  harmonic extreme points, Hansen splitting, Bendat–Sherman and measure existence.
- [Final verification evidence](verification/2026-10-11-complete/README.md):
  local build, transitive axiom reports and the manifest of 101 source hashes.

The mathematical source is George Stepaniants's
[RA-10 solution](../../../../randomized-and-low-rank-approximation/RA-10/solution.md),
Theorem 1, Lemma 2 and Sections 3–5. The representation development follows
the route discussed in [the representation note](REPRESENTATION_PROGRESS.md#reuse-audit),
using Mathlib's Krein–Milman, measure compactness and integration APIs. This
implementation was developed with OpenAI Codex assistance and adds no external
library dependency.

## Reproduce the local check

From `lean-statements/`, with the committed dependency pins:

```bash
lake exe cache get
lake build NLA.Proofs.RA10.OperatorMonotoneRepresentation NLA.Proofs.RA10.OperatorMonotoneConcavity
shasum -a 256 -c ../docs/lean/proofs/RA-10/verification/2026-10-11-complete/complete-source-sha256.txt
```

The final representation, transfer and target report only `propext`,
`Classical.choice` and `Quot.sound`. The final build passed again during PR
preparation. A separate CI step builds these candidate modules without adding
them to the reviewed proof aggregate. That build is not the independent
Comparator verification of the target; existing statement-identity checks do
not verify the target's truth.

## Fork review scope

The draft PR is intended for `FormulaRabbit81/OpenProblemsInNLA`, from
`codex/ra10-spectral-transfer` into `codex/ra10-review-base`. The review base
points to the existing upstream baseline above: the fork's `main` is 126
commits behind it, and comparing against that baseline keeps the diff specific
to this proof development. The fork's `main` is not modified.

The canonical problem, mathematical target, dependency pins and catalogue
status are unchanged. Before claiming the repository's `Lean verified`
status, the final source requires independent reviews and the proof-target
Comparator setup and isolated Linux verification described in the
[per-problem workflow](../../README.md). Older hash-bound reviews and partial
build logs remain historical evidence; they do not review these new sources.

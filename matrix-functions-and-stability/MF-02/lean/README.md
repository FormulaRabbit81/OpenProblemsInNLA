# MF-02 Lean proof

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization. Mathematical attribution is recorded in
[SourceCorrespondence.md](SourceCorrespondence.md).

The complete thirteen-target proof passed Linux development compilation and
LeanCert kernel assertions at bb3188268137f84e521763242b46251395ae2f4b.
**Standalone Comparator, default-kernel replay, controls and final review are
pending. This package does not yet promote the canonical problem's status.**
The [development run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35015144656)
failed overall on the separate IE-17 candidate; MF-02's build and statement
commands both exited zero. The full receipt and logs are retained in
[verification/development-2026-09-15](verification/development-2026-09-15).

## Scope

The formalization retains every multiplication budget and real gap 0 < δ < 1,
free real linear combinations and stored-product reuse, the true maximum
approximation error on both closed intervals, coefficient infima and an attained
natural stage minimum. It proves the original uniform constant-factor overhead,
including the two small-budget cases.

The proof uses exact polynomial identities and Mathlib's exterior Chebyshev
bound. No interval subdivision or sampled-input argument is needed. All thirteen
exports are listed in [comparator.json](comparator.json), with their source
locations and actual development axiom reports in
[formalization.yaml](formalization.yaml).

## Run the proof

From this directory with Lean installed:

```bash
lake exe cache get && lake build +Solution
```

This builds the proof with the committed toolchain and dependency revisions.
The stronger Linux checks use the repository's
[shared verification guide](../../../docs/lean/README.md). A build alone does
not run Comparator or independently establish correspondence with the informal
problem.

[Challenge.lean](Challenge.lean) deliberately contains independent statement
contracts with placeholder bodies. [Solution.lean](Solution.lean) imports the
proved graph, never Challenge, and checks every advertised export with LeanCert
kernel trust. Historical statement-phase files are retained under
[reviews/statement-phase/frozen](reviews/statement-phase/frozen); their original
draft labels are provenance, not current verification claims. The only package
configuration change after that phase selects Solution as the default target.

Two independent proof-source reviews are in
[reviews/proof-source](reviews/proof-source). Final acceptance will require
addenda binding the accepted publication source and actual standalone logs.
AI-agent review is distinct from human peer review and mechanical checking.

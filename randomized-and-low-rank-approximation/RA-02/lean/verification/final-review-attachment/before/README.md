# RA-02 Lean formalization

This candidate disproves the original polynomial trace-error guarantee after exactly the target rank of randomly pivoted Cholesky steps. For every real C>0 and p>=0, it constructs a positive-definite complex matrix of dimension r+1 whose actual expected residual trace after r steps strictly exceeds C r^p times its actual ordered eigenvalue tail. The universal target includes every positive dimension, every complex Hermitian PSD matrix, and every integer1<=r<=n.

**Actual local Lean build and two independent complete source reviews accepted; canonical Linux verification pending.** The [local acceptance](verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json) and [original command map](verification/local-development/PATH-MAP.json) identify all35 successful source-matched origins. Development19 compiled three modules afresh and reused32 exact prior successful outputs. These records do not certify unrun Linux default-kernel replay, Comparator or sandbox/rejection controls. No verification count, publication commit or PR is claimed by this private candidate.

Start with the [numerical targets](NUMERICAL_TARGETS.md), concrete [Definitions](NLA/RA02/Definitions.lean), independent [Challenge](Challenge.lean), and [source correspondence](SourceCorrespondence.md). The [active source manifest](ACTIVE-SOURCE-MANIFEST.json) and [implementation map](IMPLEMENTATION-MAP.json) identify all35 files and27 exports. Original frozen preparation documents retain their historical pending wording; [current evidence](PUBLICATION-EVIDENCE.json) records the current phase. Deliberate Challenge placeholders are separate specifications and are never imported by the proof.

The proof establishes the normalized adaptive PSD process, including zero residuals, zero-probability choices and every ordered history. It uses genuinely decreasing Hermitian eigenvalues and a Euclidean Rayleigh bound. A finite arrowhead family, exact residual identities and an injective binary history count give a sufficient factor2^r/3. This negates the full original question. The manuscript's sharper limiting factor2^r, entrywise-positive and correlation-matrix extensions, the separate LU theorem, and oversampling are not formal claims here.

The sole numerical certificate, `Real.exp 1 <= 3`, uses LeanCert kernel trust. Its result feeds the rank-dependent denominator bound, actual spectral-tail factor, and final arbitrary-real-exponent contradiction. All matrix, rank, history and exponent calculations remain symbolic; there is no interval subdivision or numerical eigenvalue approximation.

[Solution](Solution.lean) is byte-identical to the final locally tested Complete wrapper. Its import closure reaches all34 mathematical files. All nine original frozen files are retained as exact snapshots; active Lake configuration only registers and selects Solution. With pinned dependencies available, `lake build` in this directory is the local entry point. Fresh canonical Linux verification of this packaging is still pending. Development followed the user's local-first instruction: one compiler process, one thread, at most4096MiB, and only pinned source-matched successful output reuse.

From the repository root, use the shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/RA-02/lean /absolute/path/to/nla-lean-tools
```

Formalization and integration: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematical resolution: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. RPCholesky and the comparison problem retain the credit to Chen, Epperly, Tropp and Webber. Substantial OpenAI Codex assistance is disclosed; no new historical-priority claim is made.

Both [complete nonauthor reviews](reviews/INDEX.json) read every selected proof file and authenticate the recorded local evidence. The package preparer authored RA-02 statements and proofs, so its packaging checks are not an independent mathematical review. Reviewer scopes and roles are explicit; no official Tau Ceti endorsement or human peer review is asserted. Mathlib and LeanCert supply proof foundations; Schiffer and Forsythe supplied inspected structure examples. The [bounded duplicate audit](DUPLICATE-AUDIT.json) is a dated public snapshot, not a claim about unpublished or later work. [Source/privacy records](verification/OMITTED-ORIGINALS.json) distinguish raw and contact-redacted manuscript hashes. [License](LICENSE).

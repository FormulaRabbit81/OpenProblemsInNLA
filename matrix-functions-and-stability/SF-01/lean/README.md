# SF-01 Lean formalization

This formalization proves preservation of positive-diagonal real H-matrices by the original Newton iteration: X0=A and X(k+1)=(Xk+Xk^-1*A)/2. It includes every positive dimension and every k>=0, and proves actual invertibility at every step. The H predicate uses the original comparison matrix and full complex algebraic spectral radius. No symmetry, normality, positive entries, bounded iteration or supplied rational representation is assumed.

**Complete canonical Linux verification passed.** [Run 35175258802](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35175258802/job/105055517720) checked literal revision `3312b0795873cfecade03fa421a5433651d47674`, all 271 submitted inputs and all 24 targets. Default-kernel replay, Comparator, standard transitive axioms, kernel-mode LeanCert and the per-project rejection/isolation controls passed. The [retained evidence](verification/linux-35175258802/README.md), [coordinator audit](verification/linux-35175258802/ROOT-AUDIT.json) and [independent runtime review](reviews/canonical-runtime/REVIEW.md) record the executed checks. Evidence audits are not additional executions. Later publication and upstream merge checkouts require separate checks.

The preceding actual serial macOS development and reused exact successful outputs remain separately recorded in the [local acceptance](verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json) and [command-origin map](verification/local-development/PATH-MAP.json). Two complete nonauthor source reviews accepted the proof. The immutable active source manifest and original preparation records retain their pre-execution wording; current verification is recorded in PUBLICATION-EVIDENCE.json and formalization.yaml.

Read the [numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/SF01/Definitions.lean), independent [Challenge](Challenge.lean), and [source correspondence](SourceCorrespondence.md). Frozen preparation records retain historical wording; [publication evidence](PUBLICATION-EVIDENCE.json) records the current phase. All 24 exported signatures are selected by [comparator.json](comparator.json), with no replaceable definitions and only propext, Classical.choice and Quot.sound permitted. Deliberate Challenge placeholders are specifications and are never imported by the implementation.

The argument proves the spectral/positive-weight bridges, actual shifted resolvent domination, the finite rational preserver, and a finite positive-definite pole construction. Genuine block inverse identities give a new scalar data record before quantifying over input matrices and dimensions. This yields the all-iteration theorem. Empty pole families, repeated poles and zero weights remain included. Scaled/affine initializations and Halley extensions of the manuscript are outside this formal claim.

The sole interval certificate, `0 < 1/2`, is proved with LeanCert kernel trust and consumed in initialization and coefficient halving. All matrix, dimension, spectral and iteration estimates are symbolic; no interval subdivision or input sampling occurs.

[Solution](Solution.lean) retains exactly the final tested export-only wrapper bytes. Its actual import closure has 31 files; all 37 selected sources are retained, including six older independent export probes. The [active manifest](ACTIVE-SOURCE-MANIFEST.json) distinguishes them. All nine original frozen files are preserved; the only active Lake change selects the already registered Solution library. With pinned dependencies available, run `lake build` from this directory. The standalone canonical package passed the immutable Linux execution above.

From the repository root, use the shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-functions-and-stability/SF-01/lean /absolute/path/to/nla-lean-tools
```

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematics: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Sidney Holden** retains authorship and Apache-2.0 credit for the two unchanged [IV03 source files](REUSE-IV03.md), which are actually imported. Substantial OpenAI Codex assistance is disclosed. [Historical reports](reviews/INDEX.json) preserve reviewer roles and scopes; no official Tau Ceti endorsement or human peer review is asserted. Schiffer, Forsythe, Mathlib, LeanCert, Lean Comparator and formalization.yaml supplied structure and foundations. [Privacy omissions](verification/OMITTED-ORIGINALS.json) retain exact source hashes and immutable links. [License](LICENSE).

Final source approval is supplied by the [complete nonauthor referee](reviews/final/SF01-full-final-referee/REVIEW.md) and the [other nonauthor complete review chain](reviews/historical/SF01-mf22-final-newton07/REVIEW.md), continued through [repairs 11/13/14](reviews/historical/SF01-mf22-routine-local11-14/REVIEW.md) and the [last empty-sum repair](reviews/historical/SF01-mf22-routine-local15/REVIEW.md). The independent operational reviewer authored one helper and is explicitly not counted as a full nonauthor referee.

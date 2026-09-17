# SF-01 Lean formalization

This candidate proves preservation of positive-diagonal real H-matrices by the original Newton iteration: X0=A and X(k+1)=(Xk+Xk^-1*A)/2. It includes every positive dimension and every k>=0, and proves actual invertibility at every step. The H predicate uses the original comparison matrix and full complex algebraic spectral radius. No symmetry, normality, positive entries, bounded iteration or supplied rational representation is assumed.

**Actual local Lean build accepted; canonical Linux verification pending.** The [local acceptance](verification/LOCAL-DEVELOPMENT-ACCEPTANCE.json) and [command-origin map](verification/local-development/PATH-MAP.json) identify exact successful sources and logs, including reused successful local outputs. They do not certify the fresh non-root Linux sandbox, default-kernel replay, Comparator or rejection controls. Those remain separate gates. No verified count, published commit or PR is claimed by this candidate.

Read the [numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/SF01/Definitions.lean), independent [Challenge](Challenge.lean), and [source correspondence](SourceCorrespondence.md). Frozen preparation records retain historical wording; [publication evidence](PUBLICATION-EVIDENCE.json) records the current phase. All24 exported signatures are selected by [comparator.json](comparator.json), with no replaceable definitions and only propext, Classical.choice and Quot.sound permitted. Deliberate Challenge placeholders are specifications and are never imported by the implementation.

The argument proves the spectral/positive-weight bridges, actual shifted resolvent domination, the finite rational preserver, and a finite positive-definite pole construction. Genuine block inverse identities give a new scalar data record before quantifying over input matrices and dimensions. This yields the all-iteration theorem. Empty pole families, repeated poles and zero weights remain included. Scaled/affine initializations and Halley extensions of the manuscript are outside this formal claim.

The sole interval certificate, `0 < 1/2`, is proved with LeanCert kernel trust and consumed in initialization and coefficient halving. All matrix, dimension, spectral and iteration estimates are symbolic; no interval subdivision or input sampling occurs.

[Solution](Solution.lean) retains exactly the final tested export-only wrapper bytes. Its actual import closure has31 files; all37 selected sources are retained, including six older independent export probes. The [active manifest](ACTIVE-SOURCE-MANIFEST.json) distinguishes them. All nine original frozen files are preserved; the only active Lake change selects the already registered Solution library. With pinned dependencies available, run `lake build` from this directory. Standalone canonical packaging still needs actual Linux execution.

From the repository root, use the shared [Linux harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-functions-and-stability/SF-01/lean /absolute/path/to/nla-lean-tools
```

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Original mathematics: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Sidney Holden** retains authorship and Apache-2.0 credit for the two unchanged [IV03 source files](REUSE-IV03.md), which are actually imported. Substantial OpenAI Codex assistance is disclosed. [Historical reports](reviews/INDEX.json) preserve reviewer roles and scopes; no official Tau Ceti endorsement or human peer review is asserted. Schiffer, Forsythe, Mathlib, LeanCert, Lean Comparator and formalization.yaml supplied structure and foundations. [Privacy omissions](verification/OMITTED-ORIGINALS.json) retain exact source hashes and immutable links. [License](LICENSE).

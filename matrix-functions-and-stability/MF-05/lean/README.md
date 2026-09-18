# MF-05 Lean proof

This project proves the complete original local two-family Hölder continuity statement for the joint spectral radius. The main declaration is `NLA.MF05.canonical_local_holder`. Both compact complex matrix families vary after the positive neighborhood radius and Hölder constant are chosen. All positive dimensions, infinite generating families, reducibility, zero radius, and zero Hausdorff distance are included.

**Complete canonical verification passed.** All fourteen independent contracts passed local Lean compilation and two independent final source reviews, then [actual non-root Linux run 35252365986](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35252365986/job/105307710518) at proof commit `06b8cf49740205c4b7b0b71ee5c636855fbe26a6`. Comparator, Lean's default kernel, standard transitive-axiom checks and all per-proof rejection and sandbox controls passed. The [source-bound execution record](verification/linux-2026-09-17/README.md) contains the actual logs and artifact. Later publication and upstream merge checkouts are checked separately; see [STATE.json](STATE.json).

After installing the pinned Lean toolchain, a local build can be run from this directory with:

```sh
lake build
```

Dependency downloads and the first build can take time. The recorded development runs shared pinned caches and used a single compiler with one thread and at most 4096 MiB. Their source hashes, commands, logs and authenticated reuse chains are in [the local record](verification/LOCAL-COMPLETE.json). These macOS runs are not Linux sandbox or Comparator runs.

[Challenge.lean](Challenge.lean) specifies all 14 exact target statements in an independent environment; [Solution.lean](Solution.lean) imports the proofs and prints every target's transitive axioms. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The intentional Challenge placeholders are not implementation proofs and are never imported by Solution.

The [numerical-first boundary](NUMERICAL_TARGETS.md), [frozen correspondence](SourceCorrespondence.md), [contract map](CONTRACT-MAP.json), and [statement freeze](STATEMENT-FREEZE.json) retain the reviewed original target. Wording describing future obligations in those frozen planning records refers to their pre-implementation stage. Current implementation locations and actual verification status are in [formalization.yaml](formalization.yaml).

LeanCert, in kernel mode, proves the consumed bound `0 < 1/2 < 1`. Matrix dimensions, all word products, compact extrema, root limits, perturbation bounds and real-power optimization are symbolic. Twenty published MF07 source modules are copied unchanged with their namespace and attribution; only their required import closure enters this Solution. No continuity of the joint spectral radius or existence of an extremal norm is assumed.

Pinned versions: Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The pinned Schiffer and Forsythe examples informed the independent-Challenge and numerical-first structure. [Independent reviewers](reviews/README.md) applied the pinned Tau Ceti rubrics; no official Tau Ceti certification or external human peer review is claimed.

Original mathematical proof: Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization contribution: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Prior Mathlib, LeanCert and MF07 code authorship is preserved. Substantial OpenAI Codex assistance is disclosed. George Stepaniants's email is not published.

The [independent publication preflight](reviews/publication-package.md) approved the source and local evidence for the final Linux check. Its [complete audit packet](reviews/publication-package-packet.tar.gz) retains the exact reviewed package hashes and scope.

For the complete checker on a non-root Linux system with the prerequisites in the [shared harness](../../../tools/lean/HARNESS.md), run from the repository root:

```sh
tools/lean/bootstrap.sh /tmp/nla-mf05-tools
tools/lean/verify.sh matrix-functions-and-stability/MF-05/lean /tmp/nla-mf05-tools
```

This command performs the real isolated Comparator check and its controls. `lake build` is the simpler local proof build and is not a substitute for that Linux check.

The [independent nonauthor runtime audit](reviews/canonical-runtime.md) separately authenticated the published source, GitHub artifact and actual checker logs. Its read-only verifier was run by both the reviewer and coordinator; neither audit is an additional Lean execution.

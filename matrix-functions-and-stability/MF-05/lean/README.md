# MF-05 Lean proof

This project proves the complete original local two-family Hölder continuity statement for the joint spectral radius. The main declaration is `NLA.MF05.canonical_local_holder`. Both compact complex matrix families vary after the positive neighborhood radius and Hölder constant are chosen. All positive dimensions, infinite generating families, reducibility, zero radius, and zero Hausdorff distance are included.

All fourteen independently specified contracts passed actual local Lean compilation, kernel trust assertions, and standard-axiom reporting. Two independent final source reviews have approved the proof; the final GitHub Linux Comparator check remains pending; see [STATE.json](STATE.json). No completed Linux check is claimed here yet, and the canonical status remains Solved until the final Linux verification is accepted.

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

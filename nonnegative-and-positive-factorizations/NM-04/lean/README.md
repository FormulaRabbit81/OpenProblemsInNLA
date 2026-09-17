# NM-04 Lean formalization

The full Rowland-Wu coefficient identity holds for every positive real rectangular matrix with both dimensions at least one. The mathematical solution is Matthew J. Colbrook's. George Stepaniants contributes this formalization, with substantial OpenAI Codex assistance.

**Complete immutable proof verification passed.** All 35 frozen contracts passed actual local Lean204, two independent nonauthor final reviews with exact-source continuations, and [non-root Linux run 35276203784](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35276203784/job/105387449317) at proof commit `21ed3545a8b4784303e9cc0473879eb33ef4d813`. Comparator, default-kernel replay, standard transitive axioms, sandbox checks and rejection controls passed. [Execution evidence](verification/linux-2026-09-17/README.md) preserves the artifact and logs; the [local record](verification/LOCAL-COMPLETE.json) separately binds all 38 proof modules and their successful commands.

The first [Linux attempt](verification/FAILED-LINUX-35269165327.json) failed before candidate kernel replay because one derivative statement selected a different implicit continuity witness. The implementation now selects the specification's existing witness in a local section. All theorem headers and proof bodies, frozen definitions, and checker remained unchanged. Failed and successful attempts retain distinct [review records](reviews/INDEX.json). Later publication and PR merge checkouts have separate checks.

Start with [Canonical.lean](NLA/NM04/Canonical.lean), which derives the actual positive Sinkhorn null vector and the literal subset-sum coefficient identity. [Definitions](NLA/NM04/Definitions.lean), [Challenge](Challenge.lean), [Solution](Solution.lean), and the [implementation map](IMPLEMENTATION-MAP.json) identify every object and exported declaration. Challenge contains independent specification placeholders; Solution never imports it.

Positive scaling existence is proved by minimizing the real log-partition potential on a zero-sum hyperplane; uniqueness concerns the scaled matrix, with the diagonal-factor gauge treated explicitly. The determinant proof uses universal rank-one and bordered identities over commutative rings, so empty and singular minors remain included. Actual signed insertion/deletion permutations establish the four transition signs. The final theorem has no hidden nonzero-minor or fixed-dimension assumption. Convergence of a particular alternating-normalization algorithm and later manuscript extensions are outside this target.

The [numerical plan](NUMERICAL_TARGETS.md) predates all proof code. Two exact rational half inequalities execute through `interval_decide (trust := kernel)` and are both consumed by coercivity; no matrix search, interval grid, determinant-size enumeration or numerical logarithm approximation is used. Dimensions, minors and sums remain symbolic. [Source correspondence](SourceCorrespondence.md) retains the frozen original plan; [STATE.json](STATE.json) records the current stage.

With the pinned Lean toolchain and dependencies, run `lake build` here. The default target is the proof `Solution`. The final non-root Linux Comparator/default-kernel/sandbox/rejection checks use the repository's [shared harness](../../../tools/lean/HARNESS.md). The campaign uses one local compiler process, one thread and 4096 MiB; its actual bounded commands are retained. A local build does not constitute the separate Linux checks.

The Lake default now registers Solution, and the manifest's copied root label is corrected to NLANM04. [Packaging records](verification/packaging/) preserve the original metadata and exact operational change; every dependency pin and all frozen mathematical sources are unchanged. Original statement-stage wording remains historical evidence. The public scan covers current named formalization paths across upstream and visible forks; it is not an exhaustive semantic search of differently named or private work.

Formalization contributor: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**. Eric Rowland and Jason Wu retain the question, and Matthew J. Colbrook retains the mathematical solution. Mathlib, LeanCert, Comparator, Tau Ceti, Schiffer and Forsythe contributors retain their respective credit. Agent review is not external human peer review or official Tau Ceti endorsement. No email for George Stepaniants is published. [License](LICENSE).

The earlier local187 readability adjustment added only explanatory comments. Local187 recompiled its seven affected modules and reauthenticated the complete 38-module chain. [Review packets](reviews/README.md) and the original [pre-code plan](precode-01/CONTRACT-PLAN.json) preserve their original dates and scopes.

The [independent publication preflight](reviews/publication-package.md) approved the previous local187 source and local evidence for final Linux verification; it does not approve the later local204 repair. Its [complete audit packet](reviews/publication-package-packet.tar.gz) binds the reviewed package and records its scope. That preflight preceded the successful proof-commit Linux check recorded above.

For the full checker, use a non-root Linux system meeting the [shared harness prerequisites](../../../tools/lean/HARNESS.md), then run from the repository root:

```sh
tools/lean/bootstrap.sh /tmp/nla-nm04-tools
tools/lean/verify.sh nonnegative-and-positive-factorizations/NM-04/lean /tmp/nla-nm04-tools
```

This performs the actual isolated Comparator check and its controls. The simpler local `lake build` checks the proof but does not replace the Linux verification.

The repaired local204 package subsequently passed its own [preflight](reviews/package-local204.md). The successful proof-commit Linux execution also passed an [independent evidence audit](reviews/runtime-35276203784.md); its retained verifier checks exact Git inputs, artifact identity, all 35 exports and actual controls without claiming another compiler run.

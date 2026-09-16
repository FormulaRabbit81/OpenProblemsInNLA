# IE-13 Lean formalization

This complete formalization gives the exact greatest GEPP growth and its real
supremum for every original unequal natural lower/upper bandwidth pair, all
allowed dimensions, nonsingular complex banded inputs, and every legal
maximal-modulus pivot tie choice. It proves the upper bound for every active
entry and time and supplies a nonsingular rational attaining family, including
both zero-bandwidth cases. The value is 1 when p=0 and h_p(p+q) otherwise.

**Canonical verification passed for all 28 exports.** Actual non-root Linux
[run 35081003513, job 104744813757](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35081003513/job/104744813757)
checked literal proof commit `032d4c86c52ffde0c4d440f28527ba43555a0a24`
on 16 September 2026 UTC. Both independent final source/runtime referees
approved all 95 tested inputs, all 27 active mathematical files, all Comparator
matches, Lean default-kernel replay and required controls. See the
[actual evidence](verification/linux-2026-09-16/README.md) and
[complete review chain](reviews/final/README.md). Later publication-head and
upstream merge executions remain separate exact-commit checks.

Read [the numerical targets](NUMERICAL_TARGETS.md),
[definitions](NLA/IE13/Definitions.lean), [Challenge](Challenge.lean), and
[source correspondence](SourceCorrespondence.md). These frozen documents
preserve their original preparation-phase wording as historical evidence.
[Sharp](NLA/IE13/Sharp.lean) states the final greatest-value and supremum theorem;
[Solution](Solution.lean) imports the whole graph and asserts kernel trust for
every export. It never imports Challenge. Challenge's 28 deliberate placeholders
are the independent specification, not accepted proof bodies.

All dimension/bandwidth sums and recurrences remain symbolic. The consumed
LeanCert certificate in [WitnessScale](NLA/IE13/WitnessScale.lean) proves exact
half bounds with explicit kernel trust, without interval subdivision. The
actual canonical axiom reports use only propext, Classical.choice and
Quot.sound. [comparator.json](comparator.json) selects all 28 reviewed targets
and permits no definition holes.

With the pinned toolchain and dependencies available, `lake build` builds the
complete Solution. The build-only default-target change from the historical
Challenge default is recorded in the [transition](verification/packaging/TRANSITION.json).
From a fresh committed repository on supported non-root Linux, the authoritative
checker is the unchanged shared [harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-13/lean /absolute/path/to/nla-lean-tools
```

The named proof revision passed all 28 statement matches, actual default-kernel
replay, permitted-axiom audits, rejection and sandbox controls, and two final
independent source/runtime reviews. [Current metadata](formalization.yaml)
records that acceptance. The earlier [development evidence](verification/DEVELOPMENT-ACCEPTANCE.json)
remains unchanged: its IE-13 component passed while other draft projects failed.
The [publication transition](verification/publication-2026-09-16/TRANSITION.json)
preserves before-metadata bytes and all 93 other existing project inputs.
Original private review inventories are retained only
as labelled historical inventories; selected reports are under `reviews/source`.
Contact-bearing originals are linked and hashed in
[the omissions record](verification/OMITTED-ORIGINALS.json), never silently
replaced with altered bytes.

Formalization: **George Stepaniants**, Department of Computing and Mathematical
Sciences, California Institute of Technology. Original mathematical proof:
**Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical
Physics, University of Cambridge. Generic GEPP reuse from IE-14 is credited in
[the reuse record](REUSE-AUDIT.json). Substantial OpenAI Codex assistance is
disclosed. The scoped Tau Ceti review protocol is independent agent review,
without official endorsement or human peer-review claims. Schiffer and Forsythe
informed the structure. Mathlib, LeanCert and Lean Comparator supply the pinned
foundations. No contact email is supplied. [Apache 2.0 license](LICENSE).

The original statement-elaboration [receipt](statement-audit/linux/receipt.json),
[audit](statement-audit/linux/ROOT-AUDIT.json), both IE-13 component logs and
[frozen snapshots](statement-audit/snapshots) are retained byte-for-byte.
Their earlier combined run failed in unrelated draft components. These records
establish the history of the reviewed statements; later canonical acceptance is
recorded above. The historical source-correspondence description of a retained manuscript
is superseded for public packaging by the explicit manuscript omission record.

The original frozen documents, `ACTIVE-SOURCE-MANIFEST.json` and
`PACKAGE-MANIFEST.json` retain their historical candidate-phase labels. They
are immutable provenance records, not the current verification status. The
separate checker-controls job was skipped because the shared harness was
unchanged; every required per-project control ran inside the successful job.
The numerical certificate is kernel-checked once; the general proof does not
enumerate dimensions, bandwidths, pivot paths or growing intervals.

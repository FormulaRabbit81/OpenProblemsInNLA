# IE-13 Lean formalization

This complete proof candidate gives the exact greatest GEPP growth and its real
supremum for every original unequal natural lower/upper bandwidth pair, all
allowed dimensions, nonsingular complex banded inputs, and every legal
maximal-modulus pivot tie choice. It proves the upper bound for every active
entry and time and supplies a nonsingular rational attaining family, including
both zero-bandwidth cases. The value is 1 when p=0 and h_p(p+q) otherwise.

**Complete development build passed; canonical verification pending.** All28
exports and the full27-file proof graph compiled in actual non-root Linux
[run35076646177](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35076646177)
at `ce33d037e9960d7bbb096eb2bf90266cb07213c7`. The combined workflow failed in
other draft projects; IE-13's complete component passed. This is not yet
Comparator/default-kernel acceptance or an additional verified problem.

Read [the numerical targets](NUMERICAL_TARGETS.md),
[definitions](NLA/IE13/Definitions.lean), [Challenge](Challenge.lean), and
[source correspondence](SourceCorrespondence.md). These frozen documents
preserve their original preparation-phase wording as historical evidence.
[Sharp](NLA/IE13/Sharp.lean) states the final greatest-value and supremum theorem;
[Solution](Solution.lean) imports the whole graph and asserts kernel trust for
every export. It never imports Challenge. Challenge's28 deliberate placeholders
are the independent specification, not accepted proof bodies.

All dimension/bandwidth sums and recurrences remain symbolic. The consumed
LeanCert certificate in [WitnessScale](NLA/IE13/WitnessScale.lean) proves exact
half bounds with explicit kernel trust, without interval subdivision. The
actual development axiom reports use only propext, Classical.choice and
Quot.sound. [comparator.json](comparator.json) selects all28 reviewed targets
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

Canonical acceptance requires actual default-kernel replay, all28 Comparator
matches, permitted-axiom audits, rejection and sandbox controls, two final
independent source/runtime referees, and a rerun on the exact publication
commit. Current [metadata](formalization.yaml) and
[development evidence](verification/DEVELOPMENT-ACCEPTANCE.json) leave those
unobserved gates pending. Original private review inventories are retained only
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
foundations. No contact email is supplied. [Apache2.0 license](LICENSE).

# MF-06 Lean formalization

For every fixed nonempty compact family of complex matrices in every positive
finite dimension, the joint spectral radius has the original pointwise
Lipschitz lower bound against all sufficiently nearby nonempty compact families.
George Stepaniants contributes the mathematical solution and this formalization,
with substantial OpenAI Codex assistance. Epperlein and Wirth retain attribution
for the question; reused MF05/MF07 mathematics retain Matthew J. Colbrook's credit.

**All 38 frozen contracts pass actual local Lean268 through 119 modules. Final
independent reviews and the real Linux Comparator checks remain pending.**
The [local record](verification/LOCAL-COMPLETE.json) binds every source, actual
command, complete output log and chain of successful source-matched reuse.
Every export passes its kernel trust assertion with only `propext`,
`Classical.choice` and `Quot.sound`. No canonical status promotion is claimed.

Read [CanonicalLower](NLA/MF06/CanonicalLower.lean) for the final theorem,
[CriticalCompound](NLA/MF06/CriticalCompound.lean) for the exterior-power reduction,
and [ProductBoundedLower](NLA/MF06/ProductBoundedLower.lean) for the cone argument.
[Definitions](NLA/MF06/Definitions.lean), [Challenge](Challenge.lean),
[Solution](Solution.lean), and the [implementation map](IMPLEMENTATION-MAP.json)
identify all objects and exports. The independent Challenge contains specification
placeholders and is never imported by the proof.

The reference may be reducible and have unbounded normalized products. Nearby
families need not preserve its invariant subspaces. Infinite compact sets,
singular generators, zero radius, zero distance, empty words and degree-zero
exterior factors remain included. Constants are chosen before the perturbing
family. This is a pointwise one-sided bound at a fixed reference family.

The [numerical plan](NUMERICAL_TARGETS.md) and two independent statement approvals
precede implementation. All matrix dimensions, determinants, words and norm
constants remain symbolic; no interval grid or numerical spectral search is
performed. The pinned half-radius certificate uses `interval_decide (trust :=
kernel)` and is genuinely consumed in the cone and neighborhood arguments.
[Actual theorem-body inspection](verification/type-diagnostics-270/CERTIFICATE-CONSUMPTION.json)
records those references. The separate [local type diagnostic](verification/type-diagnostics-270/COMPARISON.json)
matches all 38 independently elaborated statements; it is not a Comparator run.

With the pinned toolchain and dependencies, run `lake build` here. Its default
target is `Solution`. Campaign development shares one pinned local cache and
uses at most one compiler process, one thread and 4096 MiB. On a non-root Linux
system meeting the [harness prerequisites](../../../tools/lean/HARNESS.md), run
from the repository root:

```sh
tools/lean/bootstrap.sh /tmp/nla-mf06-tools
tools/lean/verify.sh matrix-functions-and-stability/MF-06/lean /tmp/nla-mf06-tools
```

That separate harness runs the real Comparator, default-kernel replay, standard
axiom checks, sandbox checks and negative controls. No Linux success is claimed
in this local-stage package.

The [current public audit](verification/public-scope/AUDIT.json) checked target-named
formalization paths in 268 public branch heads across 15 repositories and 222
distinct commits; it found none. This is a path-based duplicate check, not a
semantic search of unrelated filenames or private/unpublished work. Immutable
tree snapshots remain retained in the campaign audit. Historical statement-stage
wording is preserved in frozen files and [archived metadata](verification/statement-history/);
[STATE.json](STATE.json) reports the current stage.

Contributor: **George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology**. Original target, background
theorems, Mathlib, LeanCert, Comparator, Tau Ceti, Schiffer and Forsythe retain
their attribution. No email for George Stepaniants is published. Agent review
does not constitute external human peer review or official Tau Ceti endorsement.
[License](LICENSE).

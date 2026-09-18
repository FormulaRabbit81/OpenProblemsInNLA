# MF-06 statement-only draft

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology. Substantial OpenAI Codex assistance.

This draft states the complete original MF-06 target. It is **not yet
typechecked, independently statement-reviewed, frozen or proved**. It does not
increase the number of Lean-verified problems.

- Read `NUMERICAL_TARGETS.md` and its source-first hash record first.
- Read `NLA/MF06/Definitions.lean`, then all 38 obligations in `Challenge.lean`.
- `SourceCorrespondence.md` maps every obligation to the full retained source.
- `STATEMENT-HEADERS.json` and `comparator.json` record the proposed exact boundary.
- `formalization.yaml` reports the unfinished statement stage.
- `SOURCE-INPUTS.json` pins copied canonical sources, prior reusable modules,
  Mathlib APIs, Tau Ceti guidance, and Schiffer/Forsythe examples.

The four MF05 contracts are selected for exact published reuse. The other 34
contracts are unproved obligations. The 38 `sorry` placeholders occur only in
independent Challenge; there is no Solution or new implementation module.
Definitions contains no proof holes or custom axioms. The old checkpoint and
the sealed pre-code packet are retained unchanged.

This is an isolated source handoff, not a standalone completed Lake project.
Its imports from existing MF05/MF07 must be assembled from the exact inert
source copies in `source-inputs/reuse` or the source-matched shared workspace.
The supplied toolchain/lake pins describe that intended assembly. No local
compiler has been started by this agent. The coordinator owns the only allowed
local compiler and will record its bounded statement-only run separately.
The Comparator configuration is prospective: Solution does not exist yet,
and no Comparator execution is claimed.

Implementation stays closed until two nonauthor statement approvals and the
coordinator's actual typecheck/freeze. The later full proof must prove every
substantial prerequisite rather than turn it into an assumption. See
`SourceCorrespondence.md` for the difficult missing foundations.

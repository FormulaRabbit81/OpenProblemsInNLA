# NM-04 Lean statement draft

This is a statement-only draft of the complete Rowland–Wu coefficient identity
for positive rectangular Sinkhorn scaling. The mathematical solution is Matthew
J. Colbrook’s; this proposed formalization credits George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, with substantial OpenAI Codex assistance.

The 35 independent specifications in [Challenge.lean](Challenge.lean) include
actual existence and uniqueness of the positive diagonal scaling, the four
literal coefficient signs, singular-valid minor identities, and the complete
canonical subset sum. [Definitions](NLA/NM04/Definitions.lean) contains concrete
functions and predicates, without proof holes or assumed scaling/minor laws.
The whole target remains every positive real m-by-n matrix with m,n at least one.

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) records the exact mathematics first.
[SourceCorrespondence.md](SourceCorrespondence.md) maps every proposed contract
to the original target or a prerequisite. The immutable [pre-code packet](precode-01/MANIFEST.json)
was prepared before any Lean source. The active definition and contract draft
is awaiting two independent source reviews and the root’s bounded local
statement typecheck. No formalization is complete, no proof implementation
exists, and no LeanCert or Comparator execution is claimed.

The dependency pins are Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.
During this statement phase, `lake build Challenge` would check specifications
with 35 deliberate proof holes; it would not verify the theorem. This preparer
has not run that command. The planned proof entrypoint is `Solution`, which
must independently import Definitions and never import Challenge.

Only the coordinator runs local Lean, with one process, one thread and a
4096 MiB limit. Proof implementation will follow accepted statements, actual
local elaboration and a recorded freeze. Two full independent proof reviews
and the real final non-root Linux Comparator/kernel/sandbox run on GitHub
will be recorded separately. No fake local sandbox is used or claimed.

The canonical problem number, path, mathematical target, solved status and
prior mathematical authorship remain unchanged. A completed formalization
will receive its own upstream pull request. This draft is not ready for
publication or a completed-target count increment.

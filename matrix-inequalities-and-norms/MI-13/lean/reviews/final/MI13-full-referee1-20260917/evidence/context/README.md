# MI-13: frozen statements for proof development

The exact Definitions and all 36 Challenge contracts have two independent
statement approvals and successful local elaboration. They are frozen in
`STATEMENT-FREEZE.json`. The coordinator must independently accept this handoff
before assigning proof implementation. No proof module or Solution exists yet.

The unchanged target is the original complex rectangular inequality, for every
`m,n >= 2`, `A,C : Matrix (Fin m) (Fin n) ℂ` and
`B : Matrix (Fin n) (Fin m) ℂ`:

```
‖ABC − CBA‖F² ≤ 2 ‖B‖op² (σ₁(A)² + σ₂(A)²) ‖C‖F².
```

The actual Euclidean Frobenius and operator norms, ordered singular values,
all ranks, repeated singular values, complex entries, and both dimension
orderings remain in scope. The internally proved refined commutator theorem
and exact block norm/spectrum transport remain substantial proof obligations.
No extra premise has been added to the final target.

Read `NUMERICAL_TARGETS.md`, `DEFINITION-AND-CONTRACT-PLAN.md`,
`NLA/MI13/Definitions.lean`, `Challenge.lean`, `SourceCorrespondence.md`,
`REVIEW-PLAN.md`, and the retained finite route under `sources/route/`.
All these mathematical and workflow files remain byte-identical to the
approved draft. The exact hash list is in `STATEMENT-FREEZE.json`.

Local run `development-20` executed Definitions and the byte-identically
transported Challenge with Lean 4.33.1, one thread and a 4096 MiB cap. Both
exited zero (17.4614 and 3.9613 seconds). Challenge emitted exactly 36 expected
placeholder warnings. The receipt and logs are under `statement-audit/local20/`;
the independent audit and two statement reports are under `statement-audit/`.
This was macOS statement elaboration. The project-level Challenge build,
proof checking, LeanCert and final Linux Comparator checks remain unrun.

The original private draft is unchanged at
`/tmp/nla-lean-next-20260915/next-statements/MI-13`. Its original manifest and
superseded status-bearing metadata are retained under `statement-history/`.
Unchanged comments in the frozen mathematical files describe their original
pre-code stage; they do not erase the later receipt or claim a proof. The
original manifest inventories the original draft, not this copied workspace.
Current status is recorded here, in `STATE.json`, `STATEMENT-FREEZE.json`, and
`formalization.yaml`, whose proved-main-results list remains empty.

Develop and debug locally before pushing, with at most one coordinator-managed
Lean compiler process, one thread, and a 4096 MiB cap. Reuse only pinned caches
and exact source-matched successful outputs. Preserve the separate Challenge
and Solution environments; Solution must never import Challenge. Any change
to mathematical definitions or contracts reopens independent statement review.

The only planned LeanCert calculation is kernel-mode strict positivity of
the exact half, consumed in Frobenius averaging; it has not run. Keep the
remaining proof symbolic and preserve all zero and deficient-rank cases.
Final acceptance requires two nonauthor proof reviews, fresh real non-root
GitHub Linux Comparator/default-kernel/sandbox/rejection controls for all
36 contracts, and exact publication correspondence. No verified count changes.

Formalization contributor: **George Stepaniants**, Department of Computing and
Mathematical Sciences, California Institute of Technology. OpenAI Codex assists
the preparation. Nobori's original question, Audenaert's established refined
commutator theorem, the repository's reduction, and library/workflow authors
retain their attribution. No email, mathematical priority, external peer review
or official Tau Ceti endorsement is claimed.

# MF-07: statements-only Lean draft

This draft proposes a formalization of the **complete original MF-07 problem**:
a dimension-only polynomial bound on every switching product from every nonempty
compact complex matrix family of joint spectral radius one.

Formalization author: **George Stepaniants**, Department of Computing and
Mathematical Sciences, California Institute of Technology. Original mathematical
proof: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical
Physics, University of Cambridge. Substantial OpenAI Codex assistance; Apache-2.0.

Only definitions and eighteen independent Challenge specifications are present.
**There is no proof implementation, statement approval, Lean compilation,
Comparator run or verified problem here.** Challenge `sorry` bodies are explicit
specification holes. `Solution.lean` intentionally does not exist. A successful
future Challenge build alone would establish only that the statements elaborate.

`NUMERICAL_TARGETS.md` was written and hashed before the Lean definitions or
Challenge. It proposes one kernel-mode LeanCert certificate, `exp(1)≤3`, consumed
to obtain a rational explicit dimension constant. Variable dimensions, word
lengths, matrices and rescaling thresholds are handled symbolically, without
interval subdivision or enumeration.

Read `SourceCorrespondence.md` for the complete source-to-statement mapping and
`CANDIDATE-COMPARISON.md` for the bounded three-candidate selection. The final
statement retains infinite compact families, the actual Euclidean operator
norm, every switching word and the original quantifier order. The infimum
formula for the JSR has a mandatory root-limit equivalence, and an identity
singleton verifies nonvacuity.

Next gates: two independent reviews of every definition and statement, actual
remote Linux statement elaboration, then an explicit immutable statement freeze.
Proof implementation begins only after those gates. Full proof acceptance later
requires independent complete-source reviews, strict kernel replay, all eighteen
Comparator matches and rejection/sandbox controls bound to the exact commit.
`REVIEW-PLAN.md` records the scoped Tau Ceti standards and future checks.

The pinned `lakefile.toml` targets Challenge for this phase. No local Lean/Lake,
cache download, Git mutation, workflow dispatch, PR, status change or verified
count increase occurred. `formalization.yaml` truthfully records unchecked work
in progress and advertises no verified main result.

This is a **private draft packet**. Raw GitHub responses, copied primary sources
and the exact historical manuscript are retained as private audit evidence and
may contain third-party contact strings. They must be scanned and omitted or
replaced by labelled hash-bound provenance before public packaging. The newly
authored definitions, statements and attribution contain no email.

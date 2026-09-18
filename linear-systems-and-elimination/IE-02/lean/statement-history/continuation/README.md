# IE-02 statement elaboration continuation 01

This separate continuation repairs one identifier spelling after the root's
actual local `development-35` failed to parse the original Definitions.
The original `/tmp/nla-lean-next-20260915/next-statements/IE-02` packet remains
byte-for-byte unchanged, manifest
`972a12860c8f7c9c0374a2ad51a9eee66104c43de333b379b3dad04eb27097ed`.

The **only Lean-source change** is literal `λ` → `lam` in Definitions and
Challenge: six character occurrences in Definitions and 38 in Challenge,
including the hypothesis name `hλ` → `hlam`. Five of the 50 headers change
spelling; the other 45 are identical. No object, expression, assumption,
quantifier, witness, degree condition, coefficient field, dimension, norm,
target, import, trust setting, dependency pin or resource setting changes.
`SOURCE-ALPHA-DIFF.patch`, `SOURCE-CHANGES.json` and
`STATEMENT-HEADERS.json` make the exact change reviewable. The old source
did not parse, so the static check establishes exact character substitution,
not parsed-AST alpha equivalence.

The actual original run used Lean 4.33.1, one process, one thread and 4096 MiB.
Definitions exited 1 with unexpected-`λ` errors at lines 153, 154 and 158.
Challenge was correctly **not run** because its dependency failed. Exact
receipt and log copies are under `evidence/local35`, with hashes in
`CONTINUATION.json`. This continuation's retry is **unrun**. No successful
statement elaboration, accepted freeze, proof implementation, Solution,
LeanCert certificate, Comparator, kernel/sandbox acceptance or publication
is claimed.

Both nonauthor reviews approved the original mathematical Definitions and
all 50 proposed contracts: `/root/sf_ra_runtime_referee` and
`/root/mi13_statement_freeze`. Their original packets are hash-bound in
`CONTINUATION.json`; their approvals are not silently transferred to these
new source bytes. Both reviewers must approve this bounded exact diff before
the root's final freeze. Root alone will run the real local retry. A later
successful statement elaboration would still not be a proof or final Linux
Comparator result.

`NUMERICAL_TARGETS.md`, `DEFINITION-AND-CONTRACT-PLAN.md`, and
`NUMERICAL-FIRST.json` are copied byte-identically, preserving the original
numerical-first record and its hashes. This continuation does not recreate
or reset that chronology. The intended single positive-half kernel LeanCert
certificate and its actual descent consumer remain unchanged future work.

The canonical target remains attained worst-case/ideal GMRES equality for
every original upper Jordan block with `n ≥ 2`, arbitrary nonzero complex
`lam`, and `1 ≤ k < n`, using actual Euclidean norms and all normalized
complex polynomials of degree at most `k`. All finite Schur, weighted
factorization, complex preservation, convexity, descent, attainment and
transport obligations remain explicit independent contracts.

`verify_draft.py` retains the original read-only static/schema checks.
`verify_continuation.py` additionally guards the complete original inventory,
the exact two-file spelling substitution, unchanged chronology and pins,
all 50 headers, original reviews, and the failed-run evidence. Actual static
commands and results are recorded in `STATIC-CHECKS.json`. They are not Lean
compilation. The author ran no Lean, Lake, cache, shared-runner mutation or
Git command. No canonical ID, path or completed-target count changes.

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, with substantial OpenAI Codex assistance.
The original Tichý–Liesen–Faber, Faber–Liesen–Tichý and Courtney–Sarason
attributions and existing library authorship/licenses remain unchanged.
No contact email is included.

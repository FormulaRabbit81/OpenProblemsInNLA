# IE-13: independent canonical runtime continuation

Reviewer and audit executor: `/root/mf22_publication_referee`.
Date: 2026-09-16 UTC. Verdict: **approve the actual canonical verification
at the exact commit below**, continuing my independent complete mathematical
source review and both canonical packaging reviews. This report does not
publish a submission, increment a count, or approve any future changed commit.

The successful execution is [GitHub run 35081003513](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35081003513),
job `104744813757`, on literal commit
`032d4c86c52ffde0c4d440f28527ba43555a0a24`. This was a push run,
not a pull-request synthetic merge. Its actual runner checkout, API head,
receipt and artifact all identify that commit. The verify and selection jobs
completed successfully. The separate `checker-controls` job was skipped for
the unchanged shared harness; the required per-project controls below actually
ran in the successful verification job.

## Independent work and source identity

I read the complete 439-line actual Comparator log, complete kernel,
regression, negative-fixture, sandbox, user-service and dependency logs, and
the bootstrap logs. I inspected the actual job diagnostics and compared all
726 nonempty emitted artifact-log lines with the raw job log. The comparison
excludes the log files' command-header and exit-status bookkeeping lines;
those lines were separately inspected and their statuses checked.

I executed the accompanying independent Python audit. Its 457 checks passed:
all **95** tracked project Git blobs exactly match both the runtime receipt
and my previously reviewed sealed package; all **27** active mathematical
source files match my complete-source review and final repair chain. All
**28** frozen Challenge contracts and their definitions, numerical obligations,
source correspondence, dependency pins and Comparator configuration remain
exact. All ten historical frozen snapshots remain exact. The only accepted
active frozen-file packaging change remains the documented Lake default
`Challenge` to `Solution`; the original Lake bytes are retained.

The unchanged proof covers the exact original sharp GEPP growth target:
complex nonsingular banded matrices, every permitted positive dimension,
every natural lower/upper bandwidth pair, all legal maximal-modulus pivot
choices, and all active entries and stages. It includes the zero lower
bandwidth case, rational sharp witnesses including zero upper bandwidth,
attainment and the actual real supremum. This continuation uses my prior
full-file mathematical readings plus exact identity checks; it does not
pretend that a runtime badge or another reviewer's verdict establishes
semantic fidelity. My complete source, final changed-file, final repair and
two packaging reviews are bound in `CHECKS.json`.

## Actual acceptance and controls

Both actual ordered export lists contain precisely the 28 configured names.
Every active module is built, all 28 exported declarations report only
`propext`, `Classical.choice`, and `Quot.sound`, and the log explicitly reports
**“Lean default kernel accepts the solution”** and **“Your solution is okay!”**.
The 28 deliberate Challenge placeholders occur before the Solution phase;
there are no proof placeholders, illegal axioms or errors in that phase.
The actual manifest/schema validator also passed with 28 declarations.

LeanCert is pinned and actually used in the built witness-scale module. Its
small exact half-bound certificate is checked once, while all bandwidth,
dimension, recurrence and witness reasoning remains symbolic. No interval
subdivision or finite computation is being substituted for the general target.

The actual built-in replay controls accepted the honest inductive/quotient
case, rejected the invalid raw proof, and rejected the quotient post-check
mismatch. All five Comparator regression cases passed their expected phases.
For precision, `simple_kind_mismatch` was rejected at its recorded illegal
`helper` axiom phase; I do not relabel that as a different observed diagnostic.
The two separate negative fixtures exited 1 as intended, rejecting `sorryAx`
and `checked._native.native_decide.ax_1_1` respectively.

Both actual sandbox modes ran as UID **1001**. The complete log establishes
private user/process/mount/network/IPC/UTS namespaces, no effective
capabilities, `no_new_privs`, denied host signalling and loopback/AF_UNIX
access, denied outer-fixture modification, build-only designated `.lake`
writability and read-only export. Nested namespace escape and all four
unexpected strict-sandbox option cases were rejected. The fixtures remained
unchanged except the designated build fixture. User-service and dependency
setup completed with their actual zero exits.

## Provenance and scope of assurance

I compared the committed shared checker and workflow with accepted harness
commit `ff6abf718126ceb23f933cf4f627f95104461fe8`; neither changed.
The source-lock digest is
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
The receipt records Linux Lean 4.33.1, core commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Forsythe checker
`8d1b0c0545a77b40245e84705aa7d273e6c81e62`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.
Every dependency revision occurs in the actual checkout log. I reconstructed
the pure CI-probe text adaptation from the committed harness and authenticated
its digest against the receipt. I did not execute that probe locally.

Artifact `10440806325` has SHA-256
`09d3534e68bdd141eaf64240b58f1bdf58ff1b225b652cb3659efabbb9ba7e73`,
matching the retained GitHub API digest. All 13 original ZIP members exactly
match the retained evidence. Root fetched the authenticated packet; I
independently read it, rehashed it and read the exact Git objects. I read the
root helper but did **not** execute it, reuse its reviewer label, alter its
`ROOT-AUDIT.json`, or use its verdict as a replacement for this audit. The
two harmless audit-preparation errors are disclosed in `ATTEMPTS.md`.

This is an independent review of the **same actual Linux execution**, not a
second independently executed Lean run or a formal proof that GitHub, Lean,
the exporter, Comparator or the platform is infallible. No local Lean/Lake
was invoked. Mathematical/source review and actual kernel/type-checking
evidence support the approval together. Publication metadata, further
commits, upstream PR execution and counting remain separate root-owned gates.

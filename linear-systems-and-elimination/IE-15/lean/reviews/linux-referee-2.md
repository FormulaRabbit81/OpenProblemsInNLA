# IE-15 independent Linux operational review — referee 2

**Verdict: PASS for actual run 35010138599 at proof commit `591690a3ca1715b61e769e7fae68cbda84565f07`, with complete correspondence to the independently reviewed proof boundary.** The retained evidence closes the Linux Comparator/kernel gate for those mathematical bytes. No blocking operational finding remains. Publication metadata must identify this exact run and preserve the source and evidence reviewed here.

Reviewer: **Codex AI agent `/root/existing_verification_audit`**, 2026-09-15; independent non-implementing statement, full-source and operational referee. I inspected the complete real Comparator log, all sandbox/checker rejection logs, the committed workflow and harness, source-lock provenance, and exact input receipt. I independently queried GitHub's jobs and artifact API and retrieved/hash-checked the pinned Comparator implementation. I did not rely on the implementer's claimed success or the other operational referee's verdict. This is an AI-agent audit, not external human peer review or official Tau Ceti endorsement.

## Evidence identity

- [Actual GitHub run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35010138599): completed successfully, attempt 1, at exact commit `591690a3ca1715b61e769e7fae68cbda84565f07`.
- Artifact **10413826406**, `lean-IE-15`: [retained ZIP](../verification/linux-2026-09-15/lean-IE-15.zip), SHA-256 `5d077ee46dd308baff55ff85b92e41097af144f224e5bdbdb389395aaca4af94`. I independently confirmed this digest through GitHub's artifact API and verified every one of its **13 file members** against the retained extracted bytes.
- [Source-hash receipt](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/result.json): SHA-256 `d191708230b0e4d30609e0ef64aa9498fb170b5c26481ee742498e25b6c7be3e`.
- [Actual Comparator log](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/comparator.log): SHA-256 `fb93cf431a5179d970d6591fb995b838929a079688f423ece68c256c9619d7b2`.
- [Independent audit evidence](linux-referee-2-evidence/audit.json): SHA-256 `83752c4971f92afacf8e4eceb7b4783d943aa8894cf4ef3e80e2951d904fc132`; records hashes of every archived evidence file, my independently fetched API responses, reviewed harness/workflow, exact target names and nine actual axiom outputs.

My independent [GitHub jobs response](linux-referee-2-evidence/github-jobs.json) and [artifact response](linux-referee-2-evidence/github-artifact.json) are retained separately from the coordinator's provenance. The digest comparison authenticates the downloaded archive against the platform's artifact record; this report does not claim a separate cryptographic signature on every compiler output.

## Binding to statements and complete reviewed source

I independently compared **all 48** receipt input hashes with both their actual Git blobs at the proof commit and the current project files at the time of this audit. Every comparison passed. The **17** core source/configuration hashes recorded in [my complete-source review evidence](final-referee-2-evidence/review-evidence.json) all agree with the actual Linux receipt.

The pre-proof [freeze record](statement-freeze.json), [statement referee 1](statement-referee-1.md), and [statement referee 2](statement-referee-2.md) remain the applicable statement boundary. Definitions, Challenge, the numerical dossier, Comparator list and dependency pins retain the frozen hashes. The sole Lakefile difference is the already independently approved default target change from Challenge to Solution. Both [final source reviews](final-referee-1.md) and [my final source review](final-referee-2.md) precede this mechanical evidence and identify the complete original target; their report files are also in the 48-file receipt.

In particular, the checked theorem pair still covers every real nonsingular input, every admissible rook-pivot path including ties, and every active entry at every stage in both dimensions. The exact witnesses, greatest elements of the genuine growth sets, and actual real supremum equalities are part of the checked exports. This review adds operational evidence to that source correspondence; successful Comparator execution alone is not being used to invent the mathematical meaning of a theorem.

## Actual Comparator execution and axioms

The log shows, in order: fresh Challenge build, Challenge export, Solution build, Solution export, `Running Lean default kernel on solution.`, `Lean default kernel accepts the solution`, `Your solution is okay!`, and **EXIT_STATUS=0**. The eight NLA names in both export lists exactly equal the frozen configuration:

1. `NLA.IE15.entryMax_semantics`
2. `NLA.IE15.all_entries_bound_three`
3. `NLA.IE15.all_entries_bound_four`
4. `NLA.IE15.witness_three`
5. `NLA.IE15.witness_four`
6. `NLA.IE15.greatest_growth_three`
7. `NLA.IE15.greatest_growth_four`
8. `NLA.IE15.exact_rook_growth`

There are no definition holes. The exact permitted-axiom set is **`propext`, `Classical.choice`, `Quot.sound`**. All eight public results and the consumed LeanCert certificate `four_le_fourteen_thirds` have actual printed axiom closures equal to this set. The eight intentional Challenge specification holes are separate from the Solution environment. No Solution hole or native axiom appears in the successful proof closure.

I independently retrieved the immutable Forsythe `Main.lean`, `Comparator/Compare.lean`, `Comparator/Axioms.lean`, and `Comparator/Util.lean` at `8d1b0c0545a77b40245e84705aa7d273e6c81e62` and matched each file's bytes and SHA-256 to the repository source lock. The inspected implementation compares target constant types and recursively compares their referenced definitions, traverses solution proof bodies and types for illegal axioms, and replays the exported solution closure with `Lean.Environment.replay` into an empty environment. It subsequently compares the quotient primitives against the replayed environment. The default kernel call is unconditional in this path, and success is printed only after comparison, axiom checking and replay return without error. No custom external-kernel claim is made.

## Freshness, sandbox and controls

The actual project log identifies an unprivileged Linux x86-64 environment, pinned Lean **4.33.1** (compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Go **1.27.1**. Bootstrap compiled the locked real Comparator, exporter and Landrun. The source lock hash is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, matching both the working repository and receipt. Executable hashes and environment/probe hashes are recorded in the bootstrap receipt. They describe the binaries checked on the runner; I did not retrieve or independently hash the runner's binary files.

I inspected the committed harness's execution order and failure handling. It validates pinned source bytes and tool receipts, runs every control, creates a fresh directory from ordinary tracked Git blobs, rejects tracked build artifacts and symlinks, checks input hashes after dependency/cache preparation, invokes the real Comparator, and checks input hashes again before writing the success receipt. The project had no imported local build objects. Dependency preparation checked out the exact locked LeanCert and Mathlib revisions. The recorded Mathlib cache downloaded/decompressed 8690 dependency files; this was a fresh **project** build, not a claim to rebuild every dependency from source. The exported dependency closure was still replayed by Lean's default kernel.

The [sandbox log](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/sandbox.log), SHA-256 `756d6d0ff96094e1b8cb9dfe0a2f85d55bc47badc80cf48e10fac7bdb90fe57c`, reports real build and export tests as UID 1001. Writes outside the designated build `.lake`, symlink escapes, network/host-process access and AF_UNIX socket creation were denied; private namespaces, no effective capabilities and `no_new_privs` were observed. Export could not write even `.lake`. Unknown options and unexpected writable-path arguments all failed with exit 2. I read the exact locked strict adapter: it wraps the real Landrun executable with Bubblewrap mount/process/network isolation and rejects those unsupported arguments. The actual Comparator command uses that adapter inside the restricted user service.

Every required rejection gate has actual evidence:

| Gate | Observed behavior |
| --- | --- |
| [Raw kernel controls](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/kernel-controls.log) | Honest inductive/quotient environment accepted; malformed raw proof rejected by default kernel; quotient mismatch rejected by post-check; suite exit 0 |
| [Comparator regressions](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/comparator-controls.log) | Honest statement accepted; constant-kind, illegal-helper and theorem-type mismatch fixtures rejected at their required phase; all five cases passed |
| [Sorry control](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/negative-sorry.log) | Both modules built/exported; `sorryAx` rejected; expected exit 1 |
| [Native control](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/negative-native.log) | Both modules built/exported; `checked._native.native_decide.ax_1_1` rejected; expected exit 1 |

The two source fixtures named `simple_axiom_issue` and `simple_kind_mismatch` are identical in the pinned suite and both reject the illegal helper. I do not count them as two distinct semantic failure modes; the separate `simple_mismatch` and added `type_mismatch` cases supply the actual kind/type checks.

My independent GitHub API read confirms that **every step of `select` and `verify (IE-15, …)` succeeded**, including manifest validation, unprivileged-isolation preparation and fresh statement/axiom/kernel verification. The separate workflow job `checker-controls` was **skipped by its documented tools-changed condition**. This does not skip a required IE-15 gate: the shared tools/workflow are byte-unchanged from the reviewed published base, and the project's `verify` function unconditionally executed all the controls above in this same artifact. It would be inaccurate to claim that every workflow job ran; it is accurate that every required project-verification gate ran successfully.

## Qualified disposition

**PASS.** The actual retained Linux evidence verifies the exact eight complete statements at the reviewed proof commit, with real isolation, working rejection controls and only the permitted axiom closure. In conjunction with the independent frozen-statement/full-source reviews and a second independent operational PASS, this evidence supports the requested **Lean verified** promotion for IE-15's complete canonical target.

I audited the actual remote run; I did not initiate a second independent Linux run or claim bit-for-bit reproduction of tool binaries on a second host. Subsequent documentation/status/attribution changes may cite this historical proof-commit receipt if the mathematical definitions, proof sources, dependency pins and verification configuration stay byte-identical. Any change to that proof boundary requires an appropriate new review and successful verification. All original targets, permanent IDs, proof attribution and previously published verifications remain outside the scope of modification by this reviewer.

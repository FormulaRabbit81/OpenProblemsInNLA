# IE-17: independent Linux operational referee 2

**Verdict: PASS for actual Linux run 35016724809, attempt 1, at proof commit `6e53192977d87097666c039f6d8134a800ff7501`.** The retained evidence passes the operational gate for the exact complete-target source previously approved. No blocking operational finding remains. This report must be combined with the independent source reviews and second operational review before status promotion.

Reviewer: **OpenAI Codex AI agent `/root/existing_verification_audit`**, 2026-09-15; independent non-implementing statement, final-source and operational referee. I inspected all twelve archived raw logs, the input receipt, workflow and harness, and independently queried GitHub for artifact and job provenance. I did not infer success from the implementer's summary or another referee's verdict. This is an AI-agent review, not external human peer review or official Tau Ceti endorsement.

## Authenticated evidence and binding

- [Actual run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35016724809), verify job **104542092686**, completed successfully at the exact commit above. My independent API result confirms attempt **1**, and every step in the `select` and IE-17 `verify` jobs completed successfully.
- Artifact **10416087458**, `lean-IE-17`: [retained ZIP](../verification/linux-2026-09-15/lean-IE-17.zip), SHA-256 `b2b2a164604c4922ebd9e614e39aa9c8dcb1d184be07e845e71adf93272c03c3`. I independently confirmed this digest and proof/run identity through GitHub's artifact API. Every one of the ZIP's **13 file members** matches the retained extracted bytes, and all **17** files in the archive's SHA256SUMS match their hashes.
- [Actual source receipt](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/result.json), SHA-256 `4224f96bf51e6ddc27ad33e2e02055526243615989580ae6adaeb18dfce67b89`.
- [Actual Comparator log](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/comparator.log), SHA-256 `0ff063d9656279e7d44fd6cc520252f89d19371d61f561724a73362223f889a9`.
- My [independent audit record](linux-referee-2-evidence/audit.json), SHA-256 `e134199e3e303b73971d7b9daf5f85c4ee3e7cb58033c22157bd545334d7737b`, records every archived evidence hash, all checks, actual target names, observed axiom closures and independently obtained [artifact](linux-referee-2-evidence/github-artifact.json)/[jobs](linux-referee-2-evidence/github-jobs.json) API responses.

I independently checked **all 69** receipt input hashes against both the actual Git blobs at the proof commit and current files. Every comparison passed. All **21** source/package inputs in my complete-source review and all **ten** pre-proof frozen inputs match the Linux receipt. Both independent statement reports, both full-source reports and their evidence are included in the committed receipt. Definitions, all proof modules, Challenge, numerical dossier, Comparator configuration and dependency pins are unchanged from the approved mathematical boundary.

The GitHub digest authenticates the retained ZIP against the platform artifact record; this is not a claim that each compiler message has a separate cryptographic signature. The report's exact hashes identify the evidence actually inspected.

## Actual statement, kernel and axiom checks

The complete log shows separate fresh Challenge and Solution builds/exports, followed by `Running Lean default kernel on solution.`, `Lean default kernel accepts the solution`, `Your solution is okay!` and **EXIT_STATUS=0**. The exported NLA names in both environments exactly equal the frozen eight-name configuration:

1. `NLA.IE17.spectralNorm_semantics`
2. `NLA.IE17.witness_full_column_rank`
3. `NLA.IE17.exact_lsmr_run`
4. `NLA.IE17.optimal_errors`
5. `NLA.IE17.approximation_values`
6. `NLA.IE17.terminal_errors_zero`
7. `NLA.IE17.both_errors_increase`
8. `NLA.IE17.canonical_counterexamples`

There are no definition holes. Every one of the **twelve actual printed axiom closures**, comprising all eight exports and four intermediate results, contains exactly `propext`, `Classical.choice`, `Quot.sound`. The Solution build has no `sorry` warning; Challenge's eight deliberate specification holes are separate. Kernel-trust assertions embedded in the freshly compiled project modules succeeded. The consumed LeanCert cutoff remains explicitly in kernel mode.

This is the same full target established in [my final source review](final-referee-2.md): true Euclidean operator norms, attained minima over every real fixed-b perturbation, complete exact LSMR minimizing semantics with minimum length and first termination, the literal four-law Moore–Penrose approximation with unique values, both terminal zero conventions, and two separate monotonicity refutations. Mechanical acceptance supplements that independent semantic review; it does not substitute for it.

## Tool provenance and freshness

The receipt identifies Lean **4.33.1**, Linux x86-64 compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Go **1.27.1**. The bootstrap logs show actual compilation of the pinned Comparator/exporter and real Landrun. Source lock SHA-256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` agrees with the committed repository and tool receipt.

I rechecked that the harness, workflow, source lock and strict sandbox remain byte-identical to the infrastructure I independently reviewed for IE-15. I also checked the whole relevant infrastructure diff against published base `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`: no change. The lock still matches the exact Forsythe Comparator Main/Compare/Axioms/Util sources I previously retrieved and inspected independently at commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62` and the same strict sandbox adapter. Their exact source hashes are in my audit record.

That implementation checks statement types and referenced definitions, traverses the solution closure for illegal axioms, replays the exported solution in Lean's default kernel from an empty environment, and checks quotient primitives afterward. The successful path cannot print acceptance before these checks. The actual rejection probes below exercise those paths in this run.

I inspected the committed harness execution order again: it validates locked source bytes, compiled-tool receipts and the probe adaptation; runs all controls; copies only ordinary tracked Git blobs to a fresh project; rejects tracked build objects and symlinks; checks inputs before and after dependency/cache preparation and after Comparator; then writes the success receipt. Both modules were built by the actual Comparator. The project's unchanged default `Challenge` Lake target does not bypass the explicit Solution build shown in this log.

The dependency log checks out the exact pinned LeanCert and Mathlib revisions. The Mathlib cache downloaded/decompressed **8690** dependency files. This is a fresh **project** build with dependency cache, not a claim that every dependency was rebuilt from source. The exported dependency closure subsequently passed default-kernel replay. The receipt records runner executable hashes; I did not independently retrieve those binary files or reproduce their bytes on a second host.

## Isolation and all rejection controls

The [sandbox log](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/sandbox.log), SHA-256 `0b511635f13e3e6771091fa34eb25bb8ed0e25bd1f9f7be6b5682330c752e41d`, demonstrates the actual build/export adapter as **UID 1001**. It observed private user, PID, mount, network, IPC and UTS namespaces, no effective capabilities and `no_new_privs`. Outside writes/truncation, symlink escape, host process access, host loopback access and AF_UNIX socket creation were denied. Build could write only its designated `.lake`; export could not write even there. Nested namespace escape attempts failed. Unknown options and all unexpected writable-path arguments failed with exit **2**. The outer fixtures were unchanged.

The actual Comparator invocation uses the locked strict adapter and a user systemd service with `RestrictAddressFamilies=~AF_UNIX`. The adapter wraps real Landrun and Bubblewrap; no fake sandbox is involved.

| Required gate | Observed result |
| --- | --- |
| [Raw replay controls](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/kernel-controls.log) | Honest inductive/quotient environment accepted; malformed raw proof rejected by the default kernel; changed quotient primitive rejected by the post-check; suite exit 0 |
| [Comparator regressions](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/comparator-controls.log) | Honest match accepted; constant-kind mismatch, illegal helper axiom and theorem-type mismatch rejected at their required phases; all five fixtures passed |
| [Sorry rejection](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/negative-sorry.log) | Both modules built/exported; `sorryAx` rejected; expected exit 1 |
| [Native rejection](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/negative-native.log) | Both modules built/exported; generated native axiom rejected; expected exit 1 |
| [User-service startup](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/user-service.log) | Restricted unprivileged service succeeded; exit 0 |

Two pinned regression fixture names both exercise the illegal-helper case; I do not count these as distinct failure mechanisms. The other fixtures separately establish kind and statement-type rejection.

The independent GitHub jobs response shows the standalone **`checker-controls` job was skipped** under its documented tools-changed condition. This is accurately distinguished from the actual IE-17 project gate: shared tools were unchanged, and **all controls above ran unconditionally inside the successful IE-17 verify job**. No required project-verification gate was skipped. It would be inaccurate to say every workflow job ran.

## Disposition and limits

**Operational PASS.** The real retained run verifies the exact eight complete reviewed targets, using working isolation, actual default-kernel replay, statement comparison and permitted-axiom controls. Combined with both independent source reviews and the second operational PASS, this supports the requested **Lean verified** promotion for IE-17.

I audited this actual remote run rather than launching a second Linux execution. Publication prose must identify the historical proof commit and run and may cite them after documentation/status updates only while the mathematical sources, pins and checker configuration remain unchanged. Metadata must update its pending-stage wording truthfully. Any substantive proof-boundary change requires appropriate renewed review and verification. This reviewer made no proof or canonical-source edits.

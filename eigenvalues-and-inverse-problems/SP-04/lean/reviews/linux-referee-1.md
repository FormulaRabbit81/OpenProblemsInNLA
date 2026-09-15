# SP-04 independent Linux operational review — referee 1

**Verdict: PASS for the actual authenticated Linux verification and all required operational controls.**

Reviewer: `/root/reference_api_review`, OpenAI GPT-6 Codex, independent non-implementing AI agent, 15 September 2026. I edited only this review and evidence. This supplements my [complete source approval](final-referee-1.md) under the [repository Tau Ceti adaptation](../../../../docs/lean/REVIEW.md). I inspected actual source, raw logs and GitHub provenance; this verdict is not inferred from a green workflow badge.

## Authenticated execution and retained archive

| Item | Independently confirmed value |
| --- | --- |
| Proof commit | `fcd722e923a339dfeee89051886e82c7384a04d7` |
| GitHub run | [35025876241](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35025876241), attempt 1, completed successfully |
| Target job | `104572782480`, `verify (SP-04, eigenvalues-and-inverse-problems/SP-04/lean)`, Ubuntu 24.04 |
| Artifact | `10419254479`, `lean-SP-04`, 18,302 bytes |
| Original ZIP SHA256 | `eae47bb19e2a64ffc99e383b204c8be89136cfe5755deb86f1e49981c9d1aa6a` |
| Receipt | `verify-20260915T213139Z-3935/result.json`, SHA256 `0cc171c644649bfa7c22ba5a80aff98a989b7b0a28519d763558bd81ad0b7bb8` |

I made my own read-only GitHub API requests for the run, target job, complete jobs list and artifact. They agree on the proof revision, run/attempt, successful target steps and artifact digest. I recomputed the ZIP hash and size, checked every one of its **13 extracted members** byte-for-byte against the permanent archive, and verified all **17 entries** in its `SHA256SUMS`. The permanent evidence is [verification/linux-2026-09-15](../verification/linux-2026-09-15/SHA256SUMS), including the [original ZIP](../verification/linux-2026-09-15/lean-SP-04.zip).

## Exact reviewed statements and source

All **88 receipt input hashes** match both current files and ordinary-file blobs at the exact proof commit. I independently enumerated the complete Git project tree: its path set equals the receipt's complete input set, with no omitted file or tracked build artifact. There are no additional current implementation modules outside that set.

All **26 final-source inputs** and **ten pre-proof frozen inputs** match their approved hashes and the receipt. The proof commit descends from the reviewed source candidate `6c351ae4a147efb82a2ede9ebc604de0683105c4`. Both complete source approvals are retained unchanged: referee 1 SHA256 `a6ceb261c1864ff1c5bbc2d432afa3e2b77a69a3ff70d1645662e7b2c152cf8d`, referee 2 SHA256 `2658c2f1611f561cbe13f0b2dd3ce87559349abd133c2b7947fc7956ae2cd758`. I read the second report in full as well as my own sealed source evidence. The original canonical/source/historical-review context and permanent registry also retain their recorded hashes. Canonical status remains **Solved** during this operational review.

The actual configuration has eleven theorem targets, no definition holes and exactly the permitted axioms `propext`, `Classical.choice`, `Quot.sound`. Both actual exports list all eleven:

`numerical_bounds`, `diagonal_stationary_iff`, `diagonal_counterexample`, `diagonal_finite`, `orthogonal_transport`, `spectral_family`, `regular_svd`, `open_family_counterexamples`, `algebraic_avoidance`, `generic_counterexamples`, `canonical_counterexample`, each in namespace `NLA.SP04`.

## Actual Comparator, kernel and axiom evidence

I read all **12 raw logs**, totaling **586 lines**. The [main log](../verification/linux-2026-09-15/verify-20260915T213139Z-3935/comparator.log) builds and exports the trusted Challenge before building Solution in the fresh project. Challenge completes 2,386 jobs and has precisely the eleven deliberate specification holes. Solution completes 3,693 jobs, builds every project proof module and has no proof-hole warning; the four known linter/deprecation notices are harmless and remain visible in the original log.

The main log then exports the complete Solution and records actual **Lean default-kernel acceptance**, Comparator's final acceptance, and exit status zero. I inspected the hash-locked `Main.verifyMatch`, `Comparator.compareAt`, `Comparator.checkAxioms` and `runBuiltinKernel` source. Acceptance follows comparison of every configured target type and recursively referenced constants, transitive illegal-axiom rejection, and replay into an initially empty Lean environment with an explicit quotient-constant post-check. The log does not print a separate line for each successful type comparison; all-eleven correspondence follows from those exact executed loops, the actual export lists, unchanged configuration and final success.

The raw Solution build prints **24 transitive axiom closures**, including all eleven exports and the numerical certificate, scalar leastness/existence, full finiteness and transport bridges. Every closure has only the three permitted axioms. The source's explicit LeanCert kernel-mode certificates and their use in the complete proof remain byte-identical to both final source approvals and were rebuilt here. The present operational verdict complements, rather than substitutes for, those source-level consumption and mathematical-correspondence checks.

## Rejection controls and real sandbox

| Control actually observed | Required result |
| --- | --- |
| Honest raw replay with inductives and quotients | Accepted by the default kernel |
| Invalid raw proof of False | Kernel rejects a declaration type mismatch |
| Quotient post-check mismatch | Kernel accepts replay, then quotient identity check rejects `Quot.lift` mismatch |
| Comparator `simple_match` | Accepted |
| Comparator `simple_mismatch` | Rejected at constant-kind comparison |
| Comparator `simple_axiom_issue` and `simple_kind_mismatch` | Both rejected for illegal `helper` axiom, as their actual logs specify |
| Comparator `type_mismatch` | Rejected for differing theorem statement |
| Separate sorry fixture | Rejected for `sorryAx`, exit 1 |
| Separate native fixture | Rejected for `checked._native.native_decide.ax_1_1`, exit 1 |

All three raw replay controls and all five Comparator regressions ran in the target verification, not merely in an unrelated historical job. The independent GitHub jobs query confirms the separate `checker-controls` job was intentionally skipped; the harness always invokes the same mandatory controls inside `verify`, and their complete actual logs are present here.

The real [sandbox log](../verification/linux-2026-09-15/verify-20260915T213139Z-3935/sandbox.log) tests both build and export modes. Writes, truncations, creation and symlink escapes outside `.lake` are denied. Build permits its designated `.lake` write; export denies `.lake` writes and truncation. User, PID, mount, network, IPC and UTS namespaces are private; the host parent is absent/inaccessible, host loopback is unreachable, AF_UNIX creation is denied, capabilities are empty and `no_new_privs` is set. Nested namespace write attempts fail. Unexpected sandbox options and writable paths all reject with exit 2, while the outer/export fixtures remain unchanged.

The actual main invocation selects the strict wrapper, pinned Comparator/exporter and the outer systemd `RestrictAddressFamilies=~AF_UNIX` restriction. I inspected the wrapper source: it invokes the pinned Landrun binary inside Bubblewrap's read-only host filesystem and private namespaces, grants only the designated build `.lake` write, and gives export no writable `.lake`. This is not a no-op sandbox receipt.

## Reproducibility and checker identity

I verified all **58 locked Forsythe tool-source files** against `source-lock.json` and the pinned repository commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The lock SHA256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`. The current harness, lock and workflow match the exact executed Git revision. The raw bootstrap logs show the actual comparator/exporter and Landrun builds.

The tool receipt identifies Linux/x86_64 Lean **4.33.1**, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Go 1.27.1, and all three executable hashes. I recomputed the adapted sandbox-probe source hash and reconstructed the environment-file hash from the actual logged invocation; both match the receipt. I inspected the harness's checks that validate the source lock, generated probe, executable hashes, environment and compiler version before controls or proof execution. The executable files are not themselves in the artifact, so I do not claim to have independently downloaded and rehashed them; their recorded validation is tied to this authenticated execution and unchanged harness.

The harness snapshots every ordinary tracked project blob from the exact Git revision into a new temporary project, excludes `.lake`/compiled artifacts, materializes the exact public dependencies and checks source hashes before and after execution. The dependency log names every pinned manifest revision, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Mathlib's dependency cache download is explicit; no prebuilt project proof replaces the fresh Solution build or kernel replay.

## Sealed reviewer evidence and disposition

The independent [audit record](linux-referee-1-evidence/audit.json), [audit script](linux-referee-1-evidence/audit.py), four fresh GitHub responses and [checksum list](linux-referee-1-evidence/SHA256SUMS) retain all **568 successful checks**, every receipt/source hash, each raw-log hash, ZIP-member hashes, all 24 axiom closures and tool identity. The script adapts my previously authored PF-02 operational audit, with the actual SP-04 paths, expected controls, declaration counts and new whole-tree checks independently inspected and executed.

Audit JSON SHA256: `207bdc5874fd3abbc8c84a0296d41ec1e4be75cc468c5ae5d3c20a520940586c`.  
Reviewer evidence checksum-list SHA256: `0763643e91b97385827faec006598c2dbb5c5f4053dafd06f95150b251ec3ec2`.

**No operational gap found.** These exact proof bytes have complete source approvals, actual eleven-target Comparator correspondence, default-kernel acceptance, permitted-axiom closure and successful reproducible isolated Linux verification with the required controls. I audited this completed hosted run; I did not execute a second Linux run on this macOS host. Canonical promotion and publication remain the coordinator's next steps after both independent operational approvals; this report itself performs neither.

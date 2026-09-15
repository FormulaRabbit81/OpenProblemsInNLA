# SP-05 independent Linux operational review — referee 1

**Verdict: PASS for the actual authenticated Linux verification and required operational controls.**

Reviewer: `/root/reference_api_review`, OpenAI GPT-6 Codex, independent non-implementing AI agent, 15 September 2026. I edited only this report and its evidence. This supplements my [full source review](final-referee-1.md) under the [repository Tau Ceti adaptation](../../../../docs/lean/REVIEW.md). I inspected actual raw logs, checker/harness source and independently queried GitHub; this verdict is not inferred from a green badge.

## Authenticated execution

| Item | Independently confirmed value |
| --- | --- |
| Proof commit | `9c8369dcea69f9f243a0502fb7e89beaa8f49fad` |
| GitHub run | [35030259545](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35030259545), attempt 1, successful |
| Job | `104586964871`, `verify (SP-05, eigenvalues-and-inverse-problems/SP-05/lean)`, Ubuntu 24.04 |
| Artifact | `10421646579`, `lean-SP-05`, 18,819 bytes |
| Original ZIP SHA256 | `bc5c29c91db0be6249c80dbfd3ca0ce2177b58c805b03935d33064bcdb25cdb1` |
| Receipt | `verify-20260915T221936Z-4220/result.json`, SHA256 `9511c2d5c9b24248c0f3e71a43225926f203b79d2064a63ced7ac1b7870354c4` |

My own four read-only GitHub API requests cover the run, full jobs list, individual target job and artifact. The returned proof revision, successful required steps, attempt, digest and ZIP size agree with the retained provenance. I recomputed the ZIP hash and matched all **13 unique extracted members** byte-for-byte to the permanent archive. They are exactly the twelve raw logs plus receipt. All **17 files** in the archive are covered by and match its checksum list.

Permanent raw evidence: [archive checksums](../verification/linux-2026-09-15/SHA256SUMS), [original ZIP](../verification/linux-2026-09-15/lean-SP-05.zip), and [receipt](../verification/linux-2026-09-15/verify-20260915T221936Z-4220/result.json).

## Frozen statement and complete source binding

All **92 receipt input hashes** match current files and exact ordinary-file Git blobs at the proof commit. An independent whole-project Git-tree enumeration has precisely the same path set, with no omitted tracked file or tracked compiled artifact. There is no additional current implementation module outside the receipt.

All **ten pre-proof frozen inputs** and **23 final-source inputs** match their approved hashes and the tested receipt. Both pre-proof reports match the freeze record. The approved candidate `081423df8a2445285261bcef2edc8fd66945f200` descends from pre-proof freeze `04d1de395494800390405f3df1645316fe7943c2`, and the Linux proof commit descends from that candidate.

Both full-source approvals remain exact: referee 1 SHA256 `b95a1710c7b0e59e64f83a35234cf878d1647552b0d22e6e9fd249939edbf533`; referee 2 SHA256 `7e280cda8973798381d9f5c02390a55e1b2e293a400173ace40edd0a8a17e036`. I read referee 2's complete report in addition to my own retained source review. Original canonical/source/historical-review context and registry retain their recorded hashes; canonical README and registry also equal published base `d8c38a795876b132c90df8d1be8682d3dcde394c` exactly. Canonical status is still **Solved** at this review.

The exact configuration has no definition holes, no optional external-kernel override, and precisely these six exports in `NLA.SP05`:

- `numerical_bound`
- `column_vectorization`
- `skew_witness`
- `positive_minimizer`
- `sector_minima`
- `canonical_result`

The mathematical fidelity, all-dimensional real/complex bridges, actual Kronecker/column vectorization, global PSD minimizer and attained symmetric/skew sector minima are covered by the two frozen statement reviews and two unchanged full-source reviews. This audit binds their exact mathematical bytes to the actual successful Linux execution.

## Actual kernel, Comparator and axiom results

I read all **12 raw logs**, totaling **616 lines**. The [main log](../verification/linux-2026-09-15/verify-20260915T221936Z-4220/comparator.log) builds trusted Challenge in **2,710 jobs**, with exactly six intentional specification holes, and exports it before building Solution. The fresh Solution build completes **3,738 jobs** and builds every project implementation module. It has no proof-hole warning; the two unused-binder linter warnings in the `sector_minima` wrapper remain visible and do not affect its type or proof.

Both actual exports list all six configured theorem targets. The log ends with actual **Lean default-kernel acceptance**, final Comparator acceptance and exit status zero. I inspected the pinned `Main.verifyMatch`, `compareIt` and `runBuiltinKernel`, together with the unchanged comparison/axiom implementation previously reviewed. Comparator checks all target types and their referenced constant definitions, traverses the proof dependencies for prohibited axioms, and replays the exported solution into an initially empty Lean environment with an explicit quotient-constant identity post-check. Successful individual comparisons are not printed separately: all-six correspondence follows from the actual export lists, exact configuration, executed loops and final success.

There are **24 raw transitive axiom closures**, including every public export, the numerical certificate, actual inverse/cone bridges, complexification, modulus comparison and the global positive minimizer. Every printed closure uses only `propext`, `Classical.choice`, `Quot.sound`, exactly the configured permitted set. The unchanged source has explicit `interval_decide (trust := kernel)` for `(0 : ℝ) < 2`, plus `#assert_trust kernel`. Its actual dependency through the full-dimensional skew witness of Frobenius square two, attained sector minima and canonical theorem was checked in the source reviews, including referee 2's compiled dependency traversal. These exact modules rebuilt successfully here; this is a consumed certificate, not a detached numerical declaration.

## Rejection controls and actual Linux sandbox

| Observed control | Actual result |
| --- | --- |
| Honest raw replay including inductives/quotients | Kernel accepts |
| Invalid raw proof of False | Kernel rejects declaration type mismatch |
| Quotient post-check mismatch | Replay accepts, then quotient post-check rejects `Quot.lift` mismatch |
| Comparator `simple_match` | Accepted, exit 0 |
| Comparator `simple_mismatch` | Rejected for differing constant kind, exit 1 |
| Comparator `simple_axiom_issue`, `simple_kind_mismatch` | Both rejected for illegal `helper` axiom, exit 1, as actually logged |
| Comparator `type_mismatch` | Rejected for differing theorem statement, exit 1 |
| Separate sorry fixture | Rejected for `sorryAx`, exit 1 |
| Separate native fixture | Rejected for `checked._native.native_decide.ax_1_1`, exit 1 |

All three raw kernel controls and all five Comparator regressions ran in this target verification. The independent complete jobs query confirms that the separate `checker-controls` job was skipped; the reviewed harness unconditionally runs its controls inside `verify` before the target snapshot, and all actual control logs are present here.

The [sandbox log](../verification/linux-2026-09-15/verify-20260915T221936Z-4220/sandbox.log) exercises both build and export modes as non-root UID 1001. It denies outside `.lake` writes, truncation, creation and symlink escape; permits the designated build `.lake` write; and denies export `.lake` writes/truncation. User, PID, mount, network, IPC and UTS namespaces are private in both modes. Host-parent discovery/signalling and host loopback fail, AF_UNIX creation fails, effective capabilities are absent and `no_new_privs` is set. Nested namespace writes fail. Four invalid option/path cases reject with exit 2; outer and export fixtures remain unchanged.

The actual target invocation uses the strict wrapper and outer systemd `RestrictAddressFamilies=~AF_UNIX`. I reread the wrapper: it invokes the pinned Landrun inside Bubblewrap's read-only host filesystem and private namespaces, with only the designated build `.lake` writable and no export write grant. This is real isolation, with actual rejection evidence, not a no-op adapter.

## Tool identity and reproducibility

All **58 locked Forsythe tool-source files** match their declared hashes/sizes and pinned commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. Source-lock SHA256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`. The current harness, lock and workflow equal their exact tested Git bytes. Bootstrap logs show actual Comparator/exporter and Landrun builds.

The receipt identifies Lean **4.33.1** for Linux/x86_64, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Go 1.27.1, and the three executable hashes. I recomputed the generated sandbox-probe source hash and reconstructed the environment-file hash from the logged invocation; both match the receipt. I reread the harness's executable, source-lock, probe, environment and compiler-version checks before controls and target execution. The Linux binaries themselves are not in the artifact: their recorded hashes are bound to this authenticated execution and validated harness, not claimed as independently downloaded/rebuilt binaries.

The harness materializes every ordinary tracked source blob into a fresh temporary project and excludes compiled files and `.lake`. It checks all source hashes after dependency materialization, dependency-cache retrieval and verification. The raw dependency log checks out every exact manifest revision, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The dependency cache is explicit; the project proof is built fresh and exported for kernel replay.

## Sealed evidence and disposition

The [audit script](linux-referee-1-evidence/audit.py), [audit record](linux-referee-1-evidence/audit.json), four independently fetched GitHub responses and [checksum list](linux-referee-1-evidence/SHA256SUMS) retain **596 successful checks**, all 92 tested input hashes, source-context hashes, each raw artifact/log hash, ZIP member hashes, 24 axiom closures and tool receipt. The script adapts my own prior SP-04 operational audit and adds complete archive-inventory, build-module, freeze ancestry and exact published canonical checks for SP-05.

Audit record SHA256: `ea3bec4092054e768f35be38cf821d0eded0741246426f08bf197c12c7fa9fe8`.  
Reviewer evidence checksum-list SHA256: `cc260d5fb5601390996a224c813e551afe7a5aeb4603ca0f608ef6a9bca14691`.

**No operational gap found.** These exact reviewed proof bytes satisfy all-six statement correspondence, default-kernel replay, permitted-axiom closure and actual isolated reproducible Linux verification with all required controls. I audited this hosted execution; I did not run a second Linux execution on this macOS host. Promotion and publication remain subsequent coordinator actions after both independent operational approvals; this report performs neither.

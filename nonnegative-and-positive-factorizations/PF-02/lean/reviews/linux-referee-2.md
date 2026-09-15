# PF-02 — independent Linux operational referee 2

**Verdict: PASS for the actual archived Linux verification of the complete reviewed PF-02 target.** No operational blocker or source-correspondence discrepancy was found. This report supplies operational approval for the exact proof bytes identified below; it does not itself edit the canonical status or publish a PR.

Reviewer: OpenAI Codex GPT-6 AI agent `/root/existing_verification_audit`, 2026-09-15. I contributed no proof or definition code. This is independent artifact/provenance/source review under [the repository Tau Ceti adaptation](../../../../docs/lean/REVIEW.md), not external human peer review or an official Tau Ceti service verdict. I inspected the actual evidence rather than accepting the coordinator's success report.

## Authenticated run and artifact

- Proof commit: **`a3e984ced348f4d8529c5d0f8f87c9be7dd979e2`**, branch `codex/lean-pf02`.
- [GitHub Actions run 35021020857](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35021020857), attempt **1**, successful.
- [Target verification job 104556550871](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35021020857/job/104556550871), Ubuntu 24.04, successful; every step succeeded.
- Artifact **10418540042**, `lean-PF-02`, original ZIP size **17,553 bytes**.
- [Original ZIP](../verification/linux-2026-09-15/lean-PF-02.zip) SHA-256: **`a62edf32bfdf4ef70abcabe572ca8fffb6ba2b0d2f4f6ddc879df99229ffb6c9`**.

I independently queried the GitHub API for the artifact, run and jobs. Those responses match the archived provenance JSON, including run/attempt, proof commit, branch, successful job and artifact digest. The ZIP hash exactly equals GitHub's advertised digest. I opened the original ZIP and compared every extracted member byte-for-byte with the permanent archive: **13 members, comprising 12 logs and the result receipt**, all identical. All **17 files** in the archive's `SHA256SUMS` match; the list covers the complete archive excluding the checksum list itself.

## Exact approved-source binding

The [actual result receipt](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/result.json) has SHA-256 **`a238d7f3dc6917b4e0a48bab47607604ab62b2b8385c892f63ff5f664c7e1fba`**. It identifies the exact commit above and project `nonnegative-and-positive-factorizations/PF-02/lean`.

I independently checked every one of its **70 input hashes** against both the current files and Git blobs at that proof commit. The receipt enumerates the complete tracked project tree at that commit. All comparisons passed. Its inputs include:

- All **20** files sealed in `reviews/final-source-inputs.json` and approved by both final source referees.
- All **10** pre-proof frozen files, unchanged from the two independently approved statements and numerical dossier.
- The exact Challenge, definitions, proof modules, Solution, Comparator configuration, pinned environment, metadata and both statement/final referee reports.

The two final source approvals applied to candidate `61561dd99c57c7334b3304fa0ad88a51eeac84f2`; the operational commit adds the review records while preserving every sealed candidate input. My [final source report](final-referee-2.md), SHA-256 `5ab463c378756cbfc6d07e65834a003a7cbb16874a4ce11dfb6909e4ff86b010`, and [referee 1's report](final-referee-1.md), SHA-256 `f16663b009aab0d6b13688a059b770c3911a133477ad637ae9761202d8c7f121`, are themselves bound by the Linux receipt. The original canonical page and complete manuscript still match their independently reviewed source hashes. Permanent ID, full original target and proof attribution remain preserved.

## Actual full-target build, Comparator and permitted axioms

I read the complete [Comparator log](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/comparator.log), SHA-256 **`f24da1c8ae5e1e4fd3f37a3f9890435fdcdf03bd7484135895bb76343551b8bf`**. It shows the fresh project path, the real strict sandbox adapter, distinct Challenge and Solution builds/exports, all project modules compiling, and final exit **0**. The nine expected placeholder warnings occur only in Challenge; the Solution build has no `sorry` warnings.

Both actual exported name lists exactly match the frozen manifest:

| Export under `NLA.PF02` | Reviewed complete-target obligation |
| --- | --- |
| `witness_data` | Positive integer matrix, determinant 8192, actual rank six, orientations ±32 |
| `witness_factorizations` | Both full trace factorizations and actual positive definite factors |
| `witness_minimal_rank` | Attained minimum PSD factor size three over every positive size |
| `orbit_semantics` | Actual quotient map and equality iff one full real invertible congruence |
| `orientation_nonvanishing` | Nonzero coordinate determinant for every factorization |
| `orientation_preserved` | Sign preserved under every real invertible congruence |
| `quotient_separation` | Continuous surjection of the complete quotient onto discrete Bool |
| `witness_disconnected` | Genuine quotient disconnectedness |
| `canonical_counterexample` | Negation of the full original universal connectedness claim |

The log then explicitly runs the **Lean default kernel**, records its acceptance, and records Comparator success. There are no replaceable definition holes. This is actual kernel replay and statement correspondence against the independently reviewed Challenge, not merely a successful `lake build` or textual signature comparison.

All **22 printed project axiom closures**, including all nine public targets, contain exactly **`propext`, `Classical.choice`, `Quot.sound`**. Comparator permits only these three and checks the exported dependency closure. The actual source retains `interval_decide (trust := kernel)` for `thirty_two_pos`, with kernel trust assertion and the same permitted axiom closure in the Linux log. The quotient-surjectivity proof consumes that certificate in both sign witnesses. Thus the LeanCert requirement is substantive and remains part of the full target's checked proof path.

## Actual rejection and isolation controls

I inspected all control logs in full, including their commands, specific acceptance/rejection reasons and exit statuses:

- [Raw kernel controls](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/kernel-controls.log): honest inductive/quotient fixture accepted; raw invalid proof rejected by the default kernel for the actual type mismatch; altered quotient constant rejected by the quotient post-check. All three actual `Comparator.runBuiltinKernel` cases behaved as required.
- [Comparator controls](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/comparator-controls.log): all five cases reached the intended phase. Honest matching succeeds; mismatched declaration kind, illicit helper axioms, and a different theorem statement are rejected. The fixture named `simple_kind_mismatch` actually rejects its illegal helper axiom, as shown by the log; the independent `simple_mismatch` case supplies the declaration-kind rejection.
- [Sorry control](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/negative-sorry.log): actual `sorryAx` rejected, exit **1**.
- [Native control](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/negative-native.log): actual `checked._native.native_decide.ax_1_1` rejected, exit **1**.
- [Sandbox control](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/sandbox.log): real build/export modes run as UID **1001** with private user/PID/mount/network/IPC/UTS namespaces, no effective capabilities and `no_new_privs`. Writes outside the designated build `.lake`, truncate and symlink escapes, host-process access, loopback and AF_UNIX socket creation, and nested namespace attempts are denied. Export mode also denies `.lake` writes. Unsupported/overbroad adapter options fail. Only the designated build fixture changes.
- [User-service control](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/user-service.log): succeeds under the actual AF_UNIX-restricted user service.

The separate workflow job named `checker-controls` was **skipped**, because shared tooling was unchanged. This is not a missing proof gate: the reviewed harness calls **all mandatory controls unconditionally inside `verify`**, before fresh project verification, and every corresponding raw log is present and passes. The selection/test job and every target-verification step succeeded. I do not describe the skipped standalone job as having run.

## Pins and reproducibility

The source lock, harness and workflow bytes match both the proof commit and the versions independently audited in this campaign:

- Source lock: `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
- Harness: `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f`.
- Workflow: `2c3963089483ec5e7e35e6355fa60988778e0b439ce099d7cd7050a8c3b6467c`.

I reread the harness's fetch/hash validation, immutable ordinary-Git-blob snapshot, source preservation checks, mandatory controls and final Comparator invocation. The locked Forsythe commit is `8d1b0c0545a77b40245e84705aa7d273e6c81e62`; the strict adapter remains locked to SHA-256 `4d6172274dd6109b1171dc01548512aa1af31f1e8fed88aa40b3c8b831345e1c`. No fake sandbox, optional replay switch or replacement source is selected. The recorded CI probe adaptation hash matches the reviewed adaptation `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`.

The three bootstrap logs show actual Comparator/exporter and Landrun builds and successful Lean toolchain setup. The receipt records Lean **4.33.1**, Linux x86-64, Go **1.27.1**, the three executable hashes and environment hash. The harness validates these values and the locked sources before use. I inspected the dependency log: every exact checkout revision matches the project manifest, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The Mathlib cache log records ordinary pinned dependency-cache retrieval. The mathematical project itself was freshly reconstructed from committed source, without tracked `.lake` objects, and all exported proof dependencies were replayed by the default kernel. This audit does not claim a source rebuild of all cached Mathlib dependencies or an independent local rebuild of the runner's executable hashes.

## Evidence and qualification

My independent [audit record](linux-referee-2-evidence/audit.json), SHA-256 **`e6f750d06139c2d4fbbd6f1e29d35ebd7cb2e1df970e29dc1240253d9acc6702`**, records authenticated API hashes, every raw archive hash, source/review hashes, all nine actual names and 22 axiom lists, tool receipt and exact check results. [The reproducible audit script](linux-referee-2-evidence/audit-artifact.py) and its [successful output](linux-referee-2-evidence/audit-artifact.log) are retained alongside the independent API responses.

This is independent review of an actual authenticated GitHub Linux run, not a second newly executed Linux build. Natural-language correspondence comes from the two sealed independent statement and final source reviews; the receipt binds their exact approved definitions/proofs to this successful run. Taken together, these gates establish complete-target correspondence, reproducible verification and the permitted-axiom check for PF-02. Publication metadata may now truthfully describe those completed gates, while retaining original proof attribution and the exact artifact provenance. This referee changed no source, canonical status or publication metadata.

# SF-01 and RA-02 actual statement-runtime audit

**Both exact statement-elaboration gates pass.** In real GitHub run **35083895041**, job **104754071378**, at literal published commit **09f9c4fd10c6e7d1efdb60eb0f43bc33ed920833**, the SF01 Definitions build and its 24-contract Challenge invocation exit 0, and the RA02 Definitions build and its 27-contract Challenge invocation exit 0. Each Challenge produces exactly one intentional `sorry` warning at each reviewed theorem declaration and no errors. These are 51 successfully elaborated specifications, not 51 proofs or two verified problems. No freeze or proof implementation is applied by this audit.

The overall GitHub conclusion is **failure**. Its two failing commands are the MI04 and MF07 proof-module builds. The checker deliberately continues to the other commands and retains each separate exit code, output hash and post-command source map. The failure is therefore compatible with the four successful statement commands; no green selector-only workflow is used as evidence.

Reviewer `/root/ie13_continuation` authored the SF01 draft and repair. This is an independently executed **operational audit**, not an independent mathematical review of that author's statements. For RA02 the reviewer did not author the draft; the earlier missing-scope observation and narrow mechanical amendment review remain disclosed. The existing independent full-statement and amendment approvals are retained as separate evidence, not replaced by this runtime report.

## Actual evidence and checks performed

I read the full four focused artifact logs and every corresponding raw job output line, the complete four amended Lean files, the prior statement and amendment reports, the actual development checker and workflow. I independently reran the inspected static helper `audit_development_run_batched.py` against the retained real run. It actually checked all **1,897 immutable Git input blobs**, all **13 command output hashes**, all post-command source maps, the exact configured command sequence and the **10 dependency revisions**. Its legacy report field still says reviewer `/root`; this invocation was by `/root/ie13_continuation`, and it asserted the existing identical ROOT-AUDIT rather than overwriting it. That unchanged report has SHA-256 `018b7da568a3e2ddbbeea9985e9eb7a7030591a285dc434705671a1226843179`.

The separately executed `audit_runtime.py` additionally checked that the Git tree and receipt input sets are equal, all 14 ZIP members equal the retained extracted files, and the artifact bytes match the GitHub API digest. Artifact **10441528405** has SHA-256 `88f876c5635c455114e86d66037bf00cca749c03ffaec6bb7cfa33ce9cd8daa8`. Run, job and artifact metadata agree on repository `sgstepaniants/OpenProblemsInNLA`, run identity and exact head. The actual compiler identifies Lean 4.33.1, x86_64 Linux, core commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; execution was non-root UID 1001. LeanCert and Mathlib match the established pins.

This task reconciled the parent's retained authenticated GitHub fetch, API records, raw job log and archive; it did not make a separate network request or rerun Lean. The source/input hashes are execution evidence, not cryptographic proof that arbitrary workflow software is infallible. Reading and binding the actual checker/workflow is part of this audit's scope.

All 13 raw command markers match the receipt in order. For each of the four focused commands, the full raw output between command boundaries matches its complete artifact log after removal of GitHub timestamps. The final RA02 boundary ends at the subsequent checker traceback; no following failure message is silently assigned to RA02. Both module logs expressly report their Definitions module built and successful build completion. Every warning line is matched against the actual theorem name's source line, and all **51 complete headers** match the approved originals and their Comparator name maps.

## Source and review boundary

The exact tested sources are:

| Project | Definitions SHA-256 | Challenge SHA-256 |
|---|---|---|
| SF01 | `937c5a9f6908fe90b9633f80aa4db1e40859a51bf37cd3bbf87729d64719057d` | `66f3111799d39aa5772dfb7395c9e95c7dc94b263d5c01d6e142f642b64c37c0` |
| RA02 | `1a0f251cfcc38f57787de3ee79dc8c89e7bf0f496ebfe9196a66f8b3f452a376` | `eb95beaddd92fc1b24d2df1d7bc9db9afec7a3391759dd2d613119c5f25d4340` |

Each equals its sealed amended source, literal published Git blob, actual receipt entry and current shared-disk file. The original SF01 18-file draft, RA02 62-file draft, SF01 12-file repair and RA02 seven-file amendment all rehash unchanged. The amendment scope remains exactly the already reviewed notation/type repairs. No declaration hypothesis, conclusion, quantifier or numeric target changed to make this run pass. Definitions contain no proof holes or custom axioms; each Challenge has exactly its intended number of placeholder bodies.

All eight relevant review inventories rehash: two original full statement approvals and two amendment approvals for each project. SF01's full statement reviewers are root and the MI04 referee; its syntax reviewers are root and the MF22 referee. RA02's full statement reviewers are root and the MI04 referee; root disclosed authorship of the preceding mathematical route, while neither authored the two Lean draft files. RA02's scope amendment reviewers are this agent and the MI04 referee, with this agent's earlier diagnostic role explicitly retained. These remain scoped agent reviews, not official external Tau Ceti endorsement or human peer review.

The tested complete source map equals the approved v2 batch's **1,897-input** planned map. The five protected checker/workflow/pin files remain equal to the approved base, and all 30 prior frozen inputs of MI04, IE13 and MF07 rehash unchanged. SF01 and RA02 have no applied statement freeze in their original draft directories. Their own unchanged toolchains and package revisions match the real shared build. The original numerical-first plans, full-target correspondence, metadata, attribution and Comparator configurations remain bound in the inventories. Name, Caltech department/university affiliation, Colbrook mathematical credit and intended Sidney Holden reuse credit are preserved; this report copies no contact-bearing API or manuscript bytes.

## Acceptance limit and next action

The two original full targets and all 51 reviewed contracts have now passed their **actual statement elaboration** prerequisite on the specified published head. Root may review and authorize a separate immutable freeze. This report does not create it or authorize proof implementation itself.

Neither project's LeanCert numerical certificate has been proved or executed by these commands. No Solution, full proof acceptance, canonical default-kernel replay, Comparator run, axiom rejection or isolation control was executed for SF01/RA02. Their future proof gates remain required, including exact publication-commit reruns. No local Lean/Lake/cache command, shared source or Git edit, publication or verified-count change occurred. The companion static audit completed successfully and binds 293 retained files; only this small private review packet was written.

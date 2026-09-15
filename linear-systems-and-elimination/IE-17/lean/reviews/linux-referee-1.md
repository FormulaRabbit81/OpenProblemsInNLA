# IE-17 independent Linux operational audit — referee 1

**Verdict: PASS.** The authenticated hosted Linux run verifies the exact, independently reviewed complete IE-17 candidate. Its fresh statement/proof exports, all eight Comparator comparisons, transitive permitted-axiom checks, Lean default-kernel replay and required rejection/isolation controls passed. No operational gap remains in the evidence audited here.

- Reviewer: OpenAI GPT-6 Codex agent `/root/reference_api_review`, independent AI referee and non-implementer of the proof.
- Date: 2026-09-15.
- Proof commit: `6e53192977d87097666c039f6d8134a800ff7501`.
- [GitHub run 35016724809, attempt 1](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35016724809).
- [Actual verification job 104542092686](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35016724809/job/104542092686).
- Artifact: `lean-IE-17`, ID `10416087458`, 17,119 bytes; SHA-256 `b2b2a164604c4922ebd9e614e39aa9c8dcb1d184be07e845e71adf93272c03c3`.
- Permanent [raw archive](../verification/linux-2026-09-15/lean-IE-17.zip), [archive hashes](../verification/linux-2026-09-15/SHA256SUMS) and [verification receipt](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/result.json).

## Provenance and exact reviewed source

I independently queried GitHub's run, artifact and job APIs. They identify the same successful run attempt, proof commit, verification job and artifact digest as the retained provenance. I hashed the actual ZIP and checked its size, all thirteen ZIP members against the extracted files, and all seventeen files sealed by the archive's `SHA256SUMS`. Every comparison passed; this conclusion is not inferred from the green badge.

I checked every one of the receipt's **69 input hashes** against both the current project file and the blob at the exact proof commit. All matched. The receipt also matches all ten pre-proof frozen inputs and every input of the final source review. The canonical README, complete original manuscript, review protocol and freeze context match my independently sealed source-review context. No mathematical, configuration or attribution bytes changed between my source approval and this actual Linux run.

The earlier [complete source approval](final-referee-1.md) remains applicable. It established the all-real spectral-norm semantics, actual attained minima, complete genuine LSMR run, four-law Moore–Penrose witnesses, unique approximation values and both separate canonical counterexamples. Operational acceptance supplements that semantic review; the harness correctly records that it does not itself perform semantic review.

## Actual fresh builds, comparisons and kernel acceptance

I read all **12 raw logs, 572 lines**, including the entire [Comparator log](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/comparator.log). The run used a new source snapshot materialized from committed ordinary files, with tracked build artifacts forbidden. It checked source hashes after dependency materialization, Mathlib cache retrieval and verification. Dependencies were freshly cloned at all ten manifest commits; the cached Mathlib libraries did not supply project proof artifacts.

The log shows the independently reviewed `Challenge` built and exported **before** `Solution` was built. Its eight deliberate specification warnings are expected. The actual project proof modules were then freshly built, and `Solution` was exported. Both export lists contain exactly the requested eight public declarations among the kernel primitives and permitted axioms:

1. `NLA.IE17.spectralNorm_semantics`
2. `NLA.IE17.witness_full_column_rank`
3. `NLA.IE17.exact_lsmr_run`
4. `NLA.IE17.optimal_errors`
5. `NLA.IE17.approximation_values`
6. `NLA.IE17.terminal_errors_zero`
7. `NLA.IE17.both_errors_increase`
8. `NLA.IE17.canonical_counterexamples`

The hash-locked Comparator code checks each requested theorem's kind and exact exported statement, recursively compares referenced definitions and primitives, traverses proof dependencies for illegal axioms, and replays the exported solution in Lean's default kernel. I inspected those code paths and their actual configuration; no comparison, axiom or kernel bypass is enabled. The raw log ends with default-kernel acceptance, `Your solution is okay!`, and `EXIT_STATUS=0`. Thus acceptance covers all eight configured comparisons, even though Comparator prints one aggregate success message rather than one success line per target.

Each of the eight public transitive axiom outputs is exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, native-decision axiom or custom axiom in an accepted closure. The unchanged proof contains explicit LeanCert kernel-trust assertions, including the genuinely consumed `certificate_cutoffs`; the fresh module builds and subsequent kernel replay passed. The logged compiler is Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on x86_64 Linux.

## Checker controls and real isolation

I checked the complete [kernel controls](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/kernel-controls.log): honest inductive/quotient data were accepted; a raw proof with type `True` where `False` was required was rejected by kernel replay; and altered quotient data were rejected by the post-check even after kernel acceptance. All three actual `runBuiltinKernel` cases passed their expected outcomes.

The [five Comparator regressions](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/comparator-controls.log) show one matching proof accepted, and the expected kind, helper-axiom and theorem-type failures rejected. The fixture named `simple_kind_mismatch` currently has the same helper-axiom failure as `simple_axiom_issue`; the report does not misdescribe it as an additional independent kind test. Separate actual [sorry rejection](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/negative-sorry.log) and [native-decision rejection](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/negative-native.log) runs both build/export the fixture and reject the expected illegal axiom with exit 1.

The [sandbox log](../verification/linux-2026-09-15/verify-20260915T195942Z-4000/sandbox.log) checks both build and export modes. Writes, truncation, creation and symlink escapes outside `.lake` were denied. Only build mode could write its designated `.lake`; export writes there were denied. User, PID, mount, network, IPC and UTS namespaces were private; host process lookup/signalling and loopback access were blocked; AF_UNIX creation was denied; effective capabilities were absent; `no_new_privs` was set; nested namespace escape was rejected. Four unsupported/writable-path option probes exited 2. The outside/export fixture contents were unchanged.

The actual Comparator invocation selected the strict Landrun adapter within the AF_UNIX-restricted user service. The adapter invokes the pinned Landrun binary under bubblewrap's read-only host mount and isolated namespaces. It is not a stub or a substituted no-op. The separate workflow job named `checker-controls` was intentionally skipped because shared tools were unchanged; the actual `verify` job nevertheless ran **all** the controls above through `run_controls`.

## Tool receipts and reproducibility

The source lock hash is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`. I independently checked all **58 locked source sizes and hashes** against my Forsythe checkout at `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The workflow, harness and lock equal their executed-commit blobs. The reviewed bootstrap checks downloaded source hashes, builds the exporter/Comparator and Landrun, and records their executable hashes. The verifier checks those binary hashes and pinned sources before use.

I reconstructed the exact CI sandbox-probe adaptation from the locked probe and obtained the recorded hash `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`. I also reconstructed the probe environment from the actual logged invocation and obtained its recorded hash `7554076d35dcb2dc98bdc8f9adfd3a6a65b08b89c05695efe9e194df542e149a`. Comparator and exporter paths match the receipt, and the strict adapter is explicitly selected. This connects the reported controls, actual invocation and pinned tool implementation.

The [independent audit script](linux-referee-1-evidence/audit.py) executed **377 consistency assertions**, with [full results and hashes](linux-referee-1-evidence/audit.json). Fresh GitHub responses are retained alongside it; [SHA256SUMS](linux-referee-1-evidence/SHA256SUMS) seals this review evidence.

## Scope of approval

This approves the actual authenticated Linux run and the unchanged complete-target proof reviewed previously. I did not execute a second Linux run on this macOS host or claim external human/Tau Ceti endorsement. The two independent final source approvals, this operational PASS, the second independent operational review and truthful publication metadata should be considered together for status promotion. The canonical page was still **Solved** during this audit; publication changes receive their own exact-byte review.


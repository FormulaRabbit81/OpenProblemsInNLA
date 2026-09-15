# IE-15 independent Linux / Comparator referee 1

**Verdict: PASS for the complete reviewed IE-15 target at commit `591690a3ca1715b61e769e7fae68cbda84565f07`.** The Linux reproduction, eight-target statement/definition comparison, permitted-axiom checks, default-kernel replay, and required positive/negative controls are supported by the actual archived outputs. No operational gap was found.

Reviewer: OpenAI GPT-6 Codex agent `/root/reference_api_review` (AI), 2026-09-15. I did not implement the IE-15 proof or the shared harness. This is independent AI review, not external human peer review. This report closes the Linux/Comparator condition left pending in my [complete source review](final-referee-1.md); it does not infer mathematical correspondence from a CI badge.

## Provenance and independently executed checks

- I read all 567 lines of the 12 raw bootstrap/verification logs, the result receipt, and the GitHub provenance files. I independently queried the public GitHub API: [run 35010138599](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35010138599), attempt 1, is completed/success at exactly the commit above; artifact `10413826406`, named `lean-IE-15`, belongs to that run and commit.
- I hashed the actual [artifact ZIP](../verification/linux-2026-09-15/lean-IE-15.zip): `5d077ee46dd308baff55ff85b92e41097af144f224e5bdbdb389395aaca4af94`, equal to the independently queried GitHub artifact digest. All 13 ZIP members equal their archived extracted bytes. The permanent archive also equals the initially downloaded files byte for byte.
- I independently compared all **48** `input_sha256` entries with both the current project files and `git show` at the verified commit: all agree. Thus the frozen Challenge, Definitions, numerical dossier, all proof modules, manifest, configuration, and source reviews are the previously approved bytes.
- I checked all **58** source-lock entries against my separate Forsythe checkout at `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, including exact sizes and SHA256 hashes. I read the actual Comparator comparison, transitive axiom traversal, kernel replay, strict sandbox wrapper, and control implementations.
- I independently reconstructed the noninteractive CI sandbox-probe bytes and the probe environment file from the actual main invocation. Their SHA256 values match the tool receipt. The receipt's source lock and executable paths match the current pinned harness and actual invocation. The harness checks source bytes, binary hashes, probe bytes, environment-file hash, and Lean version before controls and target verification; the raw bootstrap logs show the corresponding tools built successfully.
- My executed consistency audit passed **166 assertions**. Exact input, raw evidence, archive-member, harness and workflow hashes are retained in [audit.json](linux-referee-1-evidence/audit.json), SHA256 `89cefd80608b49c8d69fc62e1cf7f9b433ec8993a444e425b5d0816ece8d2060`. I additionally checked the final archive's `SHA256SUMS` against all 17 listed files.
- I inspected the subsequently archived [job provenance](../verification/linux-2026-09-15/job-provenance.json): the exact IE-15 verification job and all of its steps succeeded. The separate `checker-controls` job was skipped under the workflow's unchanged-tools condition; the actual IE-15 verification job nevertheless ran all controls, as shown by the raw logs audited below.

This is an independent audit of the actual Linux execution and its authenticated artifact, supplemented by independently executed byte/receipt checks on macOS. I did not claim to rerun Linux locally or locally rehash unavailable Linux binaries.

## Fresh build, statement matching and kernel acceptance

The reviewed harness obtains ordinary tracked source blobs directly from the verified Git commit into a fresh temporary project; it rejects tracked build artifacts and symlinks. It materializes the immutable dependency manifest, retrieves the matching Mathlib cache, and checks source hashes after each preparation step. No project Solution build precedes the Comparator's Challenge build/export.

The [main raw log](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/comparator.log) shows fresh compilation of Definitions/Challenge, Challenge export, then all local proof modules and Solution. Solution finishes successfully at 3641 build jobs. The eight deliberate Challenge `sorry` warnings are specification placeholders; none is a Solution proof acceptance. Solution uses the independent Definitions module and does not import Challenge.

Both raw exports contain all eight configured theorem targets:

1. `NLA.IE15.entryMax_semantics`
2. `NLA.IE15.all_entries_bound_three`
3. `NLA.IE15.all_entries_bound_four`
4. `NLA.IE15.witness_three`
5. `NLA.IE15.witness_four`
6. `NLA.IE15.greatest_growth_three`
7. `NLA.IE15.greatest_growth_four`
8. `NLA.IE15.exact_rook_growth`

This is one Comparator invocation covering eight independently reviewed signatures. The inspected `compareAt` code compares theorem constant types and kinds, then recursively compares their imported statement definitions and kernel primitives; `definition_names` is empty. Its successful final marker therefore covers every configured target and their statement dependencies, not only their names or the last theorem.

The raw log ends with `Running Lean default kernel on solution.`, `Lean default kernel accepts the solution`, `Your solution is okay!`, and `EXIT_STATUS=0`. The actual pinned `runBuiltinKernel` starts from an empty environment, replays the exported declarations with Lean's kernel, and post-checks the primitive quotient constants. It is not a call to `lake build` relabeled as replay.

The proof's nine `#print axioms` outputs (the eight exports plus the consumed `four_le_fourteen_thirds` certificate) each contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The actual Comparator traversal also inspects theorem/definition values, types, opaque values, inductive constructors, and recursor rules transitively. The proof explicitly uses `set_option leancert.trust "kernel"`, `leancert (trust := kernel)`, and nine `#assert_trust kernel` commands. The exact LeanCert certificate `4 ≤ 14/3` is consumed by the order-four all-stage bound, as checked in the source review and unchanged proof bytes.

## Required controls: actual observed results

| Raw control | Observation |
|---|---|
| Honest inductive/quotient raw replay | Accepted by the actual default-kernel routine. |
| Invalid raw proof (`True.intro` asserted as `False`) | Rejected while replaying `PinnedReplayProbe.invalid`, with a kernel declaration type mismatch. |
| Altered exported `Quot.lift` | Replay accepted the regenerated primitives; the distinct quotient post-check rejected the altered entry. |
| Comparator `simple_match` | Challenge/Solution exports, kernel acceptance, final success; exit 0. |
| Comparator `simple_mismatch` | Rejected for theorem/constant kind mismatch; exit 1. |
| Comparator `simple_axiom_issue` | Rejected for unpermitted `helper` axiom; exit 1. |
| Comparator `simple_kind_mismatch` | Also rejected for `helper`, which is the preserved fixture's actual behavior; no claim that it exercises a distinct kind-check phase. |
| Comparator `type_mismatch` | Rejected for unequal theorem statements; exit 1. |
| Additional `sorry` fixture | Rejected for `sorryAx`; exit 1, after both modules built/exported. |
| Additional `native_decide` fixture | Rejected for `checked._native.native_decide.ax_1_1`; exit 1, after both modules built/exported. |

See [kernel controls](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/kernel-controls.log), [Comparator controls](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/comparator-controls.log), [sorry rejection](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/negative-sorry.log), and [native rejection](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/negative-native.log). Rejection phases and error text match the actual fixtures and expected exits; these are not merely nonzero exits caused by startup failures.

## Real isolation and tool receipts

The [sandbox log](../verification/linux-2026-09-15/verify-20260915T185346Z-4171/sandbox.log) records both build and export probes at UID **1001**, under systemd's `RestrictAddressFamilies=~AF_UNIX`. I inspected the pinned wrapper: it calls `/usr/bin/bwrap --unshare-all` with read-only host mounts and then the actual compiled Landrun executable. No fake-landrun is selected.

In both modes the probes demonstrate denied outside writes/truncation/creation, denied symlink escape, private user/PID/mount/network/IPC/UTS namespaces, invisible and unsignalable host parent, unreachable host loopback, denied AF_UNIX socket creation, no effective capabilities, `no_new_privs`, and rejected nested namespace write recovery. Only the designated build `.lake` write is allowed; export `.lake` writes/truncation are denied. All outside/export fixture contents are checked unchanged. Four malformed/writable-path wrapper requests are rejected with exit 2. The raw main Comparator command selects the same strict wrapper and systemd restriction.

Recorded and matched pins include Lean `4.33.1`, Linux `x86_64`, Lean compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and Go `1.27.1`. Source-lock SHA256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`; reconstructed CI-probe SHA256 is `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`; reconstructed environment-file SHA256 is `7554076d35dcb2dc98bdc8f9adfd3a6a65b08b89c05695efe9e194df542e149a`. Binary receipt digests are retained verbatim in the archived result.

## Scope of approval

Together with my unchanged pre-proof statement and final mathematical source approvals, this evidence supports **Lean verified** for the complete IE-15 target at the stated source commit, subject to the campaign's second independent Linux review and truthful final publication metadata. It covers arbitrary permitted rook-pivot paths and all active-stage entries in orders three and four, exact attaining witnesses, and the resulting exact greatest-growth/supremum statements, as frozen before proofs. It does not formalize other campaign problems or imply external human peer review. Subsequent proof, definition, Challenge, dependency, or verifier changes require appropriate re-verification; subsequent publication metadata must accurately identify this run and source commit.

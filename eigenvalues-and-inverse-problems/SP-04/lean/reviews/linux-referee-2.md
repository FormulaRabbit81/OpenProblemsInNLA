# SP-04 independent Linux operational review — referee 2

**Verdict: PASS for the actual authenticated Linux verification of proof commit `fcd722e923a339dfeee89051886e82c7384a04d7`.** All eleven independently reviewed targets passed exact Comparator correspondence, transitive permitted-axiom checks, and Lean's default-kernel replay. The actual sandbox and required rejection controls passed. No operational blocker was found.

**Reviewer:** OpenAI Codex agent `/root/existing_verification_audit`, independent AI referee and non-implementer. **Date:** 2026-09-15. I edited only my operational review/evidence. This review applies the repository's Tau Ceti adaptation and does not claim external human review or official endorsement. Status promotion remains the coordinator's separate action after both operational reviews.

## 1. Authenticated run and original artifact

I independently queried GitHub's artifact, run, and jobs API endpoints using `gh api`, retained the three responses, and compared them with the archived provenance. The complete JSON objects agree. They identify:

- [Run 35025876241, attempt 1](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35025876241), branch `codex/lean-sp04`, exact proof commit above, workflow `.github/workflows/lean-verification.yml`, completed successfully.
- Target job **104572782480**, `verify (SP-04, eigenvalues-and-inverse-problems/SP-04/lean)`, on `ubuntu-24.04`. Every target-job step succeeded, including metadata validation, isolation preparation, the actual verification command, and artifact retention. The selection job also succeeded.
- Artifact **10419254479**, `lean-SP-04`, **18302 bytes**, not expired at review time, attached to this run and proof commit.

GitHub reports the exact SHA-256 of the original ZIP, and I independently computed the same digest from the archived bytes. All 13 ZIP members are unique and byte-identical to their extracted copies: twelve raw logs and the receipt. All 17 files listed by the archive checksum manifest match, and that list covers every raw artifact/provenance file present, excluding the checksum list itself.

| Evidence | SHA-256 |
|---|---|
| [Original `lean-SP-04.zip`](../verification/linux-2026-09-15/lean-SP-04.zip) | `eae47bb19e2a64ffc99e383b204c8be89136cfe5755deb86f1e49981c9d1aa6a` |
| [Actual `result.json`](../verification/linux-2026-09-15/verify-20260915T213139Z-3935/result.json) | `0cc171c644649bfa7c22ba5a80aff98a989b7b0a28519d763558bd81ad0b7bb8` |
| [Full actual Comparator log](../verification/linux-2026-09-15/verify-20260915T213139Z-3935/comparator.log) | `01348c806c05f219caf35f2cb52f8c30803bfd2841e7678b12935e34b9edde8f` |
| [Final candidate seal](final-source-inputs.json) | `76499435f93c35aa89fba98fa74a2c005fa3092ee769d84e9575f69f83c0ea30` |
| [Pre-proof input seal](statement-inputs.json) | `bd45a690495a0a396448925b057cf2d1e5368ba6dd2fab377f4598b5961ef7ef` |
| [Approved statement freeze](statement-freeze.json) | `e5c064933e35a22779d2628f91c682df024016fafffeefeea37fff575d4d15ed` |

## 2. Binding the actual run to the reviewed mathematics

I independently verified **all 88 receipt input hashes** against the current files and the exact Git blobs at `fcd722e923a339dfeee89051886e82c7384a04d7`. The receipt enumerates the entire tracked project at that commit, not merely selected Lean files. All 26 final-candidate inputs also match candidate commit `6c351ae4a147efb82a2ede9ebc604de0683105c4`; all ten pre-proof inputs match the approved freeze and commit `623e14e6aa93a01fca90591f96590ce79728c8f4`.

Both statement approvals and both full-source approvals are included unchanged in those 88 inputs:

| Review | SHA-256 |
|---|---|
| [Statement referee 1](statement-referee-1.md) | `02e90ae92cae849b7487c55c0891ce7a685434820d84ea3404931efa9b4af2e4` |
| [Statement referee 2](statement-referee-2.md) | `617c91bef16ca33f354bc257d9a6c0efd516ae2202ec40faeb8da0830f3706d9` |
| [Final source referee 1](final-referee-1.md) | `a6ceb261c1864ff1c5bbc2d432afa3e2b77a69a3ff70d1645662e7b2c152cf8d` |
| [Final source referee 2](final-referee-2.md) | `2658c2f1611f561cbe13f0b2dd3ce87559349abd133c2b7947fc7956ae2cd758` |

The original canonical README, full source proof/LaTeX, historical review and ID mapping remain unchanged. Their recorded hashes match the current files, proof commit and original source base `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. The subsequent published-main merge did not alter these mathematical inputs.

My earlier full-source review independently covered all fifteen NLA modules, the complete original target, a fresh Solution/Challenge build, all eleven literal signatures and 100 kernel/axiom-checked project declarations. This operational audit binds that reviewed source to the actual Linux run. It also freshly recomputes the literal Challenge-versus-Proof signature matches; all eleven are identical modulo whitespace and match my retained source-review record.

The correspondence therefore includes both determinant signs, every real stationary matrix and multiplier, the complete finite stationary set, unique least-absolute selection including ties, the literal Frobenius objective, actual distinct Gram spectrum/SVD and invertibility, the full nine-dimensional open counterexample family, every nonzero real polynomial exception, and negation of the original all-dimensions generic rule. This semantic conclusion comes from the independent source reviews; the receipt correctly says `semantic_review: not-performed-by-this-command`.

## 3. Actual target build, correspondence and kernel checks

I read the full actual `comparator.log`, not just its last success line. Comparator freshly built Challenge (2386 jobs), exported its targets, freshly built Solution (3693 jobs), exported the same targets and their dependency closures, compared declarations, checked axioms, and invoked Lean's default kernel. The only eleven `sorry` warnings occur in the deliberate Challenge specifications. Solution has no proof-hole warning; its four linter/deprecation warnings are the previously reviewed nonblocking ones.

The actual exported names from **both** modules are exactly:

```text
NLA.SP04.numerical_bounds
NLA.SP04.diagonal_stationary_iff
NLA.SP04.diagonal_counterexample
NLA.SP04.diagonal_finite
NLA.SP04.orthogonal_transport
NLA.SP04.spectral_family
NLA.SP04.regular_svd
NLA.SP04.open_family_counterexamples
NLA.SP04.algebraic_avoidance
NLA.SP04.generic_counterexamples
NLA.SP04.canonical_counterexample
```

No definition holes are configured. The allowed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. All 24 printed target/auxiliary axiom closures use exactly those three; every public target is present. The kernel-trust assertions in the actual compiled proof modules succeed. The four exact scalar inequalities are obtained with explicit LeanCert `trust := kernel` and their conjunction components are consumed in `ScalarPositive` and `ScalarRoots`, reaching the complete target. The receipt-bound proof is the same implementation whose numerical consumption was independently reviewed earlier.

The log concludes, in order, with actual default-kernel execution, acceptance, `Your solution is okay!`, and exit status 0. This is a completed Comparator run, not an ordinary Lake build being relabeled as one.

I also independently fetched and hash-checked the pinned Comparator `Main`, `Compare`, `Axioms`, `Util` and strict sandbox adapter against `source-lock.json`, then inspected their actual logic. It checks target declaration kind and type and recursively compares constants used by the statements. Axiom traversal includes theorem/opaque values and inductive/recursor dependencies. Default-kernel replay uses a fresh empty environment, then separately checks quotient constants. The builtin-kernel call is unconditional; no optional external-kernel setting substitutes for it.

## 4. All actual controls and real isolation

I read all twelve raw logs, including bootstrap, dependency materialization, cache, control, sandbox and main Comparator logs. Every positive phase ends with exit 0. The two extra negative fixtures deliberately end with exit 1 and the required rejection reasons.

| Control | Actual observed result |
|---|---|
| Honest raw proof with inductives and quotients | Default kernel accepts. |
| Invalid raw proof declaration | Default kernel rejects the True/False type mismatch. |
| Quotient post-check mismatch | Replay succeeds, then the explicit `Quot.lift` comparison rejects. |
| `simple_match` | Comparator accepts. |
| `simple_mismatch` | Comparator rejects the target declaration-kind mismatch. |
| `simple_axiom_issue` | Comparator rejects illegal axiom `helper`. |
| `simple_kind_mismatch` | Actual rejection is illegal axiom `helper`; the fixture's name does not change that observed reason. |
| `type_mismatch` | Comparator rejects the target theorem-statement mismatch. |
| Extra `sorry` fixture | Comparator rejects `sorryAx`. |
| Extra native fixture | Comparator rejects `checked._native.native_decide.ax_1_1`. |

The real sandbox probe passed in both build and export modes as non-root UID 1001. It observed private user, PID, mount, network, IPC and UTS namespaces; no effective capabilities; and `no_new_privs`. The host process was absent, host signalling lookup failed, host loopback was unreachable, AF_UNIX socket creation was denied, and nested namespace creation/write failed. Writes, truncation, creation and symlink escape outside `.lake` were denied. Only build mode could write its designated `.lake`; export mode could not. Four unexpected adapter-option/path cases were rejected with exit 2. Outer and export fixtures remained unchanged.

The strict adapter executes Bubblewrap with all namespaces unshared, the host filesystem read-only, private `/proc` and `/dev`, capabilities dropped and only the valid build `.lake` optionally writable, followed by the actual pinned Landrun. The main Comparator command uses that adapter under the systemd address-family restriction. There is no fake sandbox or macOS substitution in this evidence.

The workflow's separate `checker-controls` job is **skipped**, as its shared-tool-change condition requires. This is not a missing gate: the authenticated target job ran every mandatory control above inside `harness.verify`, before any proof work. The actual control logs and successful target-job steps establish that execution.

## 5. Reproducibility and checker provenance

The shared source lock, harness and workflow at the proof commit match the currently inspected files:

| Input | SHA-256 |
|---|---|
| `tools/lean/source-lock.json` | `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` |
| `tools/lean/harness.py` | `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f` |
| `.github/workflows/lean-verification.yml` | `2c3963089483ec5e7e35e6355fa60988778e0b439ce099d7cd7050a8c3b6467c` |

The tool receipt binds Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, Lean 4.33.1 on x86_64 Linux, Go 1.27.1, the reviewed CI probe adaptation hash `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`, the three actual checker/exporter/Landrun binary hashes, and the probe environment hash. Those exact values are retained in my audit JSON. Bootstrap logs show the pinned checker/exporter and Landrun being built successfully. Dependency logs check out every manifest commit, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

I inspected the unchanged harness's checks: locked source byte counts/hashes, tool executable/environment hashes, actual compiler version, fail-closed Linux/non-root requirements, and the exact CI probe adaptation. Its snapshot accepts only ordinary tracked Git blobs, excludes `.lake` and compiled artifacts, and checks every input again after dependency setup, cache retrieval and Comparator. The actual run used the pinned Mathlib dependency cache; it did not reuse project proof build artifacts. The logs show the project sources compiled inside the fresh snapshot by Comparator.

The committed README/metadata retain their conservative pre-operational stage wording as historical run inputs. They make no premature Linux-success claim. Canonical status was still Solved during this audit. Publication prose and status changes may accurately cite this completed evidence after the second operational approval; they must preserve the frozen statements, mathematical proofs and original attributions.

## 6. Independent evidence and limits

My executable [artifact audit](linux-referee-2-evidence/audit-artifact.py), [audit result](linux-referee-2-evidence/audit.json), independent GitHub API responses, authenticated checker-source copies and their checksum seal are retained under `linux-referee-2-evidence/`. The script was executed successfully against the current archive and reports all 88 current/Git inputs, both freezes, all eleven literal/exported signatures, 24 standard-axiom closures and all actual controls passing. Every raw archive file's digest is recorded there.

This is an independent audit of an authenticated completed Linux run, **not a second newly executed Linux build**. The binary hashes are authenticated runner receipt values; I did not reproduce Linux binary builds locally. Dependency cache reuse is disclosed. Source-to-original mathematical correspondence is supplied by the separate exact-byte statement and full-source reviews, all now bound to this run. No external human endorsement, novelty certification, or additional unexecuted check is claimed.

**Final operational disposition: PASS for the exact proof commit and artifact above. No proof changes requested.**

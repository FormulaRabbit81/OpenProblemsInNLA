# SP-05 independent Linux operational review — referee 2

**Verdict: PASS for the actual authenticated Linux verification of proof commit `9c8369dcea69f9f243a0502fb7e89beaa8f49fad`.** All six independently reviewed targets passed exact Comparator correspondence, transitive permitted-axiom checks, and Lean's default-kernel replay. The actual sandbox and required rejection controls passed. No operational blocker was found.

**Reviewer:** OpenAI Codex GPT-6 agent `/root/existing_verification_audit`, independent AI referee and non-implementer. **Date:** 2026-09-15. I edited only my operational review/evidence. This applies the repository's Tau Ceti adaptation, without claiming external human review or official endorsement. Promotion is the coordinator's separate action after both operational reviews.

## 1. Authenticated run and original artifact

I independently queried GitHub's artifact, run, and jobs endpoints using `gh api`, retained the three responses, and compared their complete objects with the archive. The archived job provenance is the single target-job object; it agrees exactly with that job selected from my independently retrieved full jobs response.

- [Run 35030259545, attempt 1](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35030259545): branch `codex/lean-sp05`, exact proof commit above, workflow `.github/workflows/lean-verification.yml`, completed successfully.
- Target job **104586964871**, `verify (SP-05, eigenvalues-and-inverse-problems/SP-05/lean)`, on `ubuntu-24.04`. Every target-job step succeeded, including metadata validation, isolation preparation, actual verification and artifact retention. The selection job succeeded.
- Artifact **10421646579**, `lean-SP-05`, **18819 bytes**, not expired at review time, attached to this run and commit.

The independently computed original ZIP digest equals GitHub's artifact digest. All 13 unique ZIP members are byte-identical to their extracted copies: twelve raw logs and the receipt. All 17 files listed in the archive checksum manifest match, and that list covers every artifact/provenance file present except the checksum list itself.

| Evidence | SHA-256 |
|---|---|
| [Original ZIP](../verification/linux-2026-09-15/lean-SP-05.zip) | `bc5c29c91db0be6249c80dbfd3ca0ce2177b58c805b03935d33064bcdb25cdb1` |
| [Actual receipt](../verification/linux-2026-09-15/verify-20260915T221936Z-4220/result.json) | `9511c2d5c9b24248c0f3e71a43225926f203b79d2064a63ced7ac1b7870354c4` |
| [Full actual Comparator log](../verification/linux-2026-09-15/verify-20260915T221936Z-4220/comparator.log) | `5db0fa9366500c1de28be102f7bb1b6cb172fa23855df54bc2b502e98c579bc2` |
| [Final candidate seal](final-source-inputs.json) | `e2f04725624543606dbf1041a756385822944051ab9d1dac8557dbd35385c0e6` |
| [Pre-proof input seal](statement-inputs.json) | `69efa93665a3cbaaf26037402329e8d9f7aa552358e5e300dbfaf27af71e0e89` |
| [Approved statement freeze](statement-freeze.json) | `933958e3661dddac9e4a9b600d9d5c0532ef6b19df4fd5d7eaa585210b0ead78` |

## 2. Binding this run to the approved mathematics

I independently verified **all 92 receipt input hashes** against current files and exact Git blobs at the proof commit. The receipt lists the entire tracked project at that commit. All 23 final-candidate inputs also match candidate commit `081423df8a2445285261bcef2edc8fd66945f200`; all ten pre-proof inputs match the approved freeze and commit `04d1de395494800390405f3df1645316fe7943c2`.

Both pre-proof approvals and both full-source approvals are unchanged receipt inputs:

| Review | SHA-256 |
|---|---|
| [Statement referee 1](statement-referee-1.md) | `44b38ebec15587dfd53174dc040be6806a42ab70ec3afd5054bd9cdc1beec96c` |
| [Statement referee 2](statement-referee-2.md) | `7c20df0a8af3245e0c04219c0631fe7b020a8760fcf60588a01c64acf285149f` |
| [Final source referee 1](final-referee-1.md) | `b95a1710c7b0e59e64f83a35234cf878d1647552b0d22e6e9fd249939edbf533` |
| [Final source referee 2](final-referee-2.md) | `7e280cda8973798381d9f5c02390a55e1b2e293a400173ace40edd0a8a17e036` |

All seven original source files in `reviews/initial/source-hashes.json` match the current files, proof commit and source base `d8c38a795876b132c90df8d1be8682d3dcde394c`. This includes the complete canonical README, source solution, PDFs/LaTeX and historical review. The permanent SP-05 ID/path mapping is preserved.

The packaging-only change from `d644e7897bd9b4fa9933b78a1e9f5116c90b6cf0` to the actual proof commit adds four byte-identical raw JSON trace payloads under `.trace.json` names, plus the support README/checksum update. My sealed [packaging supplement](packaging-referee-2.md), SHA `44574e2dddaf8314a4277ebc8ff578a8065b17673cfa237150ed1b09272297c7`, already checked all four against the older committed checksum manifest, the six-path Git delta, and unchanged candidate/freeze/source approvals. All four payloads are now in the actual Linux receipt and exact Git tree. The supplement itself was written later and is not misrepresented as a receipt input.

My prior source review independently checked the complete original target, all twelve NLA modules, a fresh Challenge/Solution build, six fully elaborated exact signatures, 81 kernel/axiom-checked declarations, and compiled proof-expression dependency traversal proving numerical-certificate consumption. This audit binds that reviewed source to the actual run and freshly compares all six literal Challenge/Proof types; they are identical modulo whitespace.

In particular the bound source covers every real positive-definite pair in every original dimension `n ≥ 2`, both actual attained sector minima, their comparison, and the stronger nonzero real PSD global minimizing eigenmatrix for `n ≥ 1`. Literal column vectorization, the actual Kronecker product and commutation permutation, genuine squared Frobenius/dot-product normalization, full complex Hermitian inverse positivity, real singular modulus, and both nonempty sectors were independently reviewed. This is source-review evidence; the receipt truthfully says `semantic_review: not-performed-by-this-command`.

## 3. Actual build, exact correspondence, kernel and axioms

I read the full actual Comparator log. It freshly builds Challenge (**2710 jobs**), exports the six targets, builds Solution (**3738 jobs**), exports the same targets/dependency closure, compares declarations, checks axioms and invokes Lean's default kernel. The only six `sorry` warnings belong to the intentional Challenge statements. Solution has no proof-hole warning; its two unused-argument linter warnings in `sector_minima` are nonblocking.

Both actual export lists contain exactly:

```text
NLA.SP05.numerical_bound
NLA.SP05.column_vectorization
NLA.SP05.skew_witness
NLA.SP05.positive_minimizer
NLA.SP05.sector_minima
NLA.SP05.canonical_result
```

There are no configured definition holes. The permitted axioms are exactly `propext`, `Classical.choice` and `Quot.sound`. All **24** printed public/auxiliary closures contain exactly those three, including every public target. The actual compiled kernel-trust assertions succeed. LeanCert's single `0 < 2` certificate explicitly uses `interval_decide (trust := kernel)`. Its use in `skew_frobenius_pos` in `Basic.lean` establishes nonzero skew witnesses and therefore actual skew-sector attainment; my earlier compiled-dependency traversal reaches the certificate from `skew_witness`, `sector_minima` and `canonical_result`. The certificate and traversal evidence are receipt-bound unchanged.

The actual log ends in this order: `Running Lean default kernel on solution.`, `Lean default kernel accepts the solution`, `Your solution is okay!`, and `EXIT_STATUS=0`. This is actual completed Comparator verification, not an ordinary local Lake build relabeled as Comparator.

I independently fetched and hash/size-checked the pinned Comparator `Main`, `Compare`, `Axioms`, `Util` and strict sandbox adapter against the source lock, then inspected their code. Comparator checks target declaration kind/type and recursively compares constants in statement dependencies. Axiom traversal visits theorem and opaque values as well as inductive/recursor dependencies. Default-kernel replay uses a fresh empty environment and separately checks quotient constants. The default-kernel call is unconditional.

## 4. Required controls and real sandbox

I read all twelve raw logs, including bootstrap, dependencies/cache, controls, sandbox and main verification. Every positive phase exits 0; the two extra negative fixtures deliberately exit 1 with the required reasons.

| Actual test | Observed result |
|---|---|
| Honest raw proof, inductives and quotients | Default kernel accepts. |
| Invalid raw proof | Default kernel rejects the True/False type mismatch. |
| Quotient post-check mismatch | Kernel replay succeeds, then explicit `Quot.lift` comparison rejects. |
| `simple_match` | Comparator accepts. |
| `simple_mismatch` | Target declaration-kind mismatch rejected. |
| `simple_axiom_issue` | Illegal axiom `helper` rejected. |
| `simple_kind_mismatch` | Actual rejection is illegal axiom `helper`; the fixture label does not change the observed reason. |
| `type_mismatch` | Actual theorem-statement mismatch rejected. |
| Extra sorry fixture | Illegal `sorryAx` rejected. |
| Extra native fixture | Illegal `checked._native.native_decide.ax_1_1` rejected. |

Both real build/export sandbox probes run as non-root UID 1001. They establish private user/PID/mount/network/IPC/UTS namespaces, no effective capabilities and `no_new_privs`; host process lookup/signalling is denied, host loopback is unreachable, AF_UNIX socket creation is denied, and nested namespace writes fail. Outside `.lake`, file writes, truncation, creation, read-only truncation and symlink escape fail. Only build mode can write its designated `.lake`; export mode cannot. All four unsupported option/path cases exit 2. Outer and export fixtures remain unchanged.

The inspected adapter actually invokes Bubblewrap with all namespaces unshared, host files read-only, private `/proc` and `/dev`, dropped capabilities and only the authorized build `.lake` writable, followed by pinned Landrun. The actual main command uses that adapter under systemd's address-family restriction. The service probe succeeds. No fake sandbox or macOS substitution is used.

The workflow's separate `checker-controls` job is **skipped** under its shared-tool-change condition. All mandatory controls above nevertheless execute inside the authenticated target job's `harness.verify` before proof verification; their actual logs and successful job steps establish that no required gate was skipped.

## 5. Reproducibility and checker provenance

The following inspected shared files match their exact Git blobs at the proof commit:

| Input | SHA-256 |
|---|---|
| `tools/lean/source-lock.json` | `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` |
| `tools/lean/harness.py` | `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f` |
| `.github/workflows/lean-verification.yml` | `2c3963089483ec5e7e35e6355fa60988778e0b439ce099d7cd7050a8c3b6467c` |

The receipt binds Forsythe `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` on x86_64 Linux, Go 1.27.1, and CI probe hash `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`. It records the actual rebuilt Comparator/exporter/Landrun binary hashes and environment hash; I verified these exact values and retain them in the audit JSON. Actual bootstrap logs show checker/exporter and Landrun builds succeeding. Dependency logs materialize every one of the ten exact manifest commits, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

I inspected the harness's source byte/hash checks, executable/environment receipt checks, actual compiler-version check, Linux/non-root requirements, and probe adaptation. Its snapshot uses ordinary tracked Git blobs, rejects dirty tracked source/symlinks/compiled artifacts, excludes `.lake`, and rechecks every input after dependency setup, cache retrieval and Comparator. The run uses the pinned Mathlib dependency cache (8690 files); the proof project is compiled from the fresh source snapshot inside Comparator. No project proof artifacts are reused.

The README and metadata remain their truthful historical candidate-stage bytes in this receipt; the canonical status remains Solved during review. The original Colbrook proof attribution and George Stepaniants's Department of Computing and Mathematical Sciences, California Institute of Technology formalization affiliation are preserved, with no added contact email. Publication updates must preserve the frozen mathematical source and state the actual evidence accurately.

## 6. Independent evidence, scope and final disposition

The executable [artifact audit](linux-referee-2-evidence/audit-artifact.py), [successful audit log](linux-referee-2-evidence/audit.log), [complete audit result](linux-referee-2-evidence/audit.json), independent GitHub API responses, authenticated checker-source copies and [checksum seal](linux-referee-2-evidence/SHA256SUMS) are retained. The executed audit checks GitHub provenance/digest, 13 ZIP members, 17 archived hashes, all 92 current/Git inputs, both seals, all six literal/exported targets, all 24 standard-axiom closures, and every actual required control. It records every raw artifact digest.

This is an independent audit of an authenticated completed Linux run, **not a second newly executed Linux build**. Binary hashes are authenticated runner values; I did not rebuild Linux binaries locally. Dependency-cache reuse is disclosed. Natural-language mathematical correspondence comes from the separate exact-byte statement/full-source reviews now bound to the run. No external human endorsement or unexecuted check is claimed.

**Final operational disposition: PASS for the exact proof commit and artifact above. No proof changes requested.**

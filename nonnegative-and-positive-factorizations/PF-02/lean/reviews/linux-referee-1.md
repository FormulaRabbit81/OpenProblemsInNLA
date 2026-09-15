# PF-02 independent Linux operational referee 1

**Verdict: PASS — the authenticated Linux run verifies all nine reviewed PF-02
exports with the pinned Comparator, Lean default kernel and permitted axioms,
and executes the required rejection and isolation controls.** No operational
gap was found. This audit makes no source or canonical-status change.

- **Reviewer:** OpenAI GPT-6 Codex agent `/root/reference_api_review`, independent
  non-implementing AI referee; 15 September 2026.
- **Protocol:** repository [Tau Ceti adaptation](../../../../docs/lean/REVIEW.md).
  Mathematical fidelity and proof quality are covered separately by my sealed
  [final source review](final-referee-1.md). This report audits actual operational
  evidence and its correspondence to those approved bytes.
- **Proof commit:** `a3e984ced348f4d8529c5d0f8f87c9be7dd979e2`.
- **Run:** [35021020857, attempt 1](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35021020857).
- **Target job:** [104556550871](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35021020857/job/104556550871),
  `verify (PF-02, nonnegative-and-positive-factorizations/PF-02/lean)`, Ubuntu 24.04.
- **Artifact:** `10418540042`, `lean-PF-02`, 17553 bytes.

I inspected the actual **12 raw logs, 603 lines**, the result receipt, retained
GitHub provenance, source lock, actual relevant Comparator/export/sandbox code,
and the workflow/harness at the proof commit. I did not infer acceptance from
the green badge or an implementer's PASS assertion.

## Independent authentication and source correspondence

I independently queried GitHub's artifact, run and job API endpoints. They
confirm the exact proof SHA, branch, attempt, successful job and steps, artifact
association, size and digest. The artifact's GitHub digest equals the SHA256 of
the retained original ZIP:

```text
a62edf32bfdf4ef70abcabe572ca8fffb6ba2b0d2f4f6ddc879df99229ffb6c9
```

I compared every one of its **13 file members** byte-for-byte with the extracted
archive. All matched. All **17** entries in the permanent archive's
[SHA256SUMS](../verification/linux-2026-09-15/SHA256SUMS) also matched. That
manifest's own SHA256 is
`43ba494a92308dbe8cb993160591cfba593042ade5394cd63033518d5a7252dd`.
The [original ZIP](../verification/linux-2026-09-15/lean-PF-02.zip), three
provenance responses and extracted raw logs remain in
`verification/linux-2026-09-15/`.

The actual [receipt](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/result.json)
has SHA256 `a238d7f3dc6917b4e0a48bab47607604ab62b2b8385c892f63ff5f664c7e1fba`.
I checked **all 70** input hashes against both current files and the proof
commit's Git objects. All matched. They include all **20** final candidate
inputs and all **ten** pre-proof frozen inputs, with no mathematical,
configuration or documentation change from the reviewed candidate. Original
canonical/manuscript context hashes also remain unchanged. Both independently
authored source reports are retained in this receipt.

The pinned harness snapshots ordinary tracked files directly from the recorded
Git commit, excludes tracked build artifacts and checks input hashes after
dependency setup, cache acquisition and Comparator execution. The main log
uses a fresh `nla-fresh-proof-…/project` directory. Challenge is built and
exported before Solution is built. This is not verification against a locally
stale proof artifact.

## Actual nine-target verification

The [Comparator log](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/comparator.log)
contains the actual separate Challenge and Solution export lists. Both contain
all nine frozen public targets:

```text
NLA.PF02.witness_data
NLA.PF02.witness_factorizations
NLA.PF02.witness_minimal_rank
NLA.PF02.orbit_semantics
NLA.PF02.orientation_nonvanishing
NLA.PF02.orientation_preserved
NLA.PF02.quotient_separation
NLA.PF02.witness_disconnected
NLA.PF02.canonical_counterexample
```

The actual receipt configuration equals the reviewed `comparator.json`: nine
targets, no definition holes and only `propext`, `Classical.choice` and
`Quot.sound` permitted. The pinned `compareAt` implementation compares every
target's constant kind and full statement, then recursively compares constants
used by those types; the required kernel primitive definitions are also checked.
The log has a single aggregate success rather than nine separate PASS lines.
Its two actual export lists, exact configuration and checked fail-fast source
establish coverage of every listed target.

Challenge built successfully in **2062 jobs**, with its nine deliberate
specification placeholders. Solution built successfully in **3649 jobs**,
including all actual proof modules and the consumed LeanCert kernel certificate.
No Solution sorry warning appears. The log prints **22** transitive axiom lists,
including all nine public exports and the actual `thirty_two_pos` theorem;
each contains only the three permitted foundational axioms. The separate
Comparator `checkAxioms` traverses the exported theorem proof dependencies and
rejects every unpermitted axiom.

The raw log then records:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
EXIT_STATUS=0
```

The reviewed `runBuiltinKernel` replays the exported declaration environment
from an empty Lean environment. Its quotient handling removes the constants
that the kernel regenerates and then checks the resulting quotient constants
against the export. The aggregate success is printed only after statement
comparison, transitive axiom validation, kernel replay and quotient post-check
all succeed. Thus this is actual default-kernel replay of the exported proof,
not only ordinary local compilation.

## Rejection controls and real isolation

I read the actual control outputs, including their failure messages and exits:

| Control | Observed behavior |
| --- | --- |
| Honest raw replay with inductives and quotients | Accepted. |
| Invalid raw proof of False | Default kernel rejected a declaration type mismatch. |
| Altered quotient export | Kernel replay completed, then quotient post-check rejected `Quot.lift`. |
| `simple_match` | Accepted through default-kernel replay. |
| `simple_mismatch` | Rejected the actual constant-kind mismatch. |
| `simple_axiom_issue` | Rejected the illegal `helper` axiom. |
| `simple_kind_mismatch` | Rejected `helper`; this retained fixture exercises an axiom violation despite its name. |
| `type_mismatch` | Rejected the different actual theorem statement `checked`. |
| Deliberate sorry proof | Exit 1, illegal `sorryAx`. |
| Deliberate native proof | Exit 1, illegal `checked._native.native_decide.ax_1_1`. |

The [raw kernel controls](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/kernel-controls.log)
call the actual `Comparator.runBuiltinKernel`. All three behaved as required.
The [five Comparator regressions](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/comparator-controls.log)
actually built and exported their Challenge and Solution modules; all expected
outcomes occurred. Both additional proof-axiom rejection logs contain the
expected real error phase, rather than a coincidental setup failure.

The [sandbox log](../verification/linux-2026-09-15/verify-20260915T204142Z-4353/sandbox.log)
executes real build and export probes as non-root UID **1001**. Both report
private user, PID, mount, network, IPC and UTS namespaces, no effective
capabilities and `no_new_privs`. Outside writes, truncation, creation and
symlink escapes are denied. Only the designated build `.lake` write succeeds;
export `.lake` writes and truncation fail. The host parent is absent from
private `/proc`, parent signaling cannot find it, host loopback is unreachable,
AF_UNIX creation is denied and nested namespace write attempts fail.

Four malformed sandbox invocations reject unknown options, an unexpected
`--rw`, an unexpected `--rwx` and a relative writable path, each with exit 2.
Outer and export fixture contents remain unchanged. The actual main invocation
selects `strict_landrun.py` and the outer
`RestrictAddressFamilies=~AF_UNIX` systemd service. Source inspection confirms
the adapter invokes real Landrun through Bubblewrap with read-only host mounts,
private namespaces and the constrained build mount. No sandbox substitute or
test double was used.

The separate workflow job named `checker-controls` was intentionally skipped
because shared tools were unchanged. This does not omit the controls: the
actual target `verify` command unconditionally ran all controls above, and its
raw logs are retained in this artifact.

## Pinned tools, dependencies and receipt consistency

The authenticated receipt records Lean **4.33.1**, x86_64 Linux, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Go **1.27.1**; Linux
`6.17.0-1022-azure`. Dependency logs show fresh checkouts of all ten manifest
revisions, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Mathlib's exact dependency
cache was downloaded; project proofs were subsequently built under isolation.

I checked all **58** locked checker/exporter/Landrun/probe files against the
independently obtained Forsythe checkout at
`8d1b0c0545a77b40245e84705aa7d273e6c81e62`. Every file size and SHA256 matched.
The actual infrastructure matches the proof commit:

| Input | SHA256 |
| --- | --- |
| Source lock | `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` |
| Harness | `f81767a17973956fbe9e5765c664d4639cce15ddf8c106f70cdcb32151808c2f` |
| Workflow | `2c3963089483ec5e7e35e6355fa60988778e0b439ce099d7cd7050a8c3b6467c` |

I independently regenerated the exact noninteractive sandbox-probe adaptation
and matched its receipt hash
`31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803`.
I also reconstructed the selected environment file from the actual main
invocation and matched its sealed hash
`7554076d35dcb2dc98bdc8f9adfd3a6a65b08b89c05695efe9e194df542e149a`.
The actual command paths agree with the receipt's Comparator and exporter
paths. Bootstrap logs show both binaries and Landrun built successfully.
The checked harness hashes all three binaries after bootstrap and validates
their hashes, source files and selected Lean version before running controls
or the target. I do not claim to have independently rebuilt the Linux binaries
on this macOS host.

## Retained independent audit and limits

The [independent evidence](linux-referee-1-evidence/README.md) contains my fresh
GitHub API responses, audit program and its detailed record. The program passed
**389 consistency checks** covering provenance, ZIP bytes, all source inputs,
checker source files, environment, all target exports and raw control phases.
The audit-record SHA256 is
`5f24ed5f61e56cdb76ca07e929644423fb0dc572915858342a5a7089713ac72d`.

This is an independent audit of the actual authenticated hosted Linux run,
not a claim that I launched a second Linux run. The semantic full-target
approval remains the separately sealed source review, whose exact inputs are
the inputs verified here. This report closes operational review #1; the other
independent operational review and a review of final publication-stage metadata
remain the coordinator's next gates. No claim of human peer review, official
Tau Ceti endorsement, source modification or status promotion is made here.

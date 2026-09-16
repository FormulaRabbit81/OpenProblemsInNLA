# MF-22 independent canonical-runtime addendum

Reviewer: `/root/mf22_publication_referee`, an independent nonimplementing AI-agent mathematical referee. Reviewed 16 September 2026 UTC.

**Verdict: approve the actual canonical runtime evidence for the complete, previously reviewed MF-22 proof at `c701bfeea660473fc31ad9d0c74b76309be3b49f`.** This is an audit of observed execution, not a promise that a future check will succeed.

The separate [complete-source review](../REVIEW.md), SHA-256 `bbbfdec513fc330f35895d5d07a3eadc31bb97f317bc8a52c33576e01d8ed274`, read all 29 active mathematical source files, the complete original problem and informal manuscript, all 22 independently frozen Challenge statements, and all ten frozen boundary files. Its associated source checks have SHA-256 `d9bda16fb6cf028b2edde19d5bffdd905963d902a683f290aed362369c6605b7`. This addendum does not replace that mathematical review.

## Observed execution and exact source binding

[GitHub run 35053254275](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35053254275), verify job `104658059786`, succeeded on Linux at the literal proof commit above. Artifact `10429509734`, `lean-MF-22.zip`, has SHA-256 `09569ed6a546db076f38bbfae867dbdc278a398c78811175dfbc4371fd7433ca`. I independently matched every one of its 13 extracted members to the ZIP, all 634 tracked project input hashes to that commit's Git blobs, and all 29 previously reviewed mathematical source hashes to these inputs. The actual raw GitHub job reports this checkout and artifact digest.

I read the entire 559-line Comparator log, every per-project control and dependency log, all three tool-bootstrap logs, the actual verification receipt, the GitHub run/job identities and the root audit. The executable `check_runtime.py` independently cross-matched 765 substantive verification-log lines to the timestamped raw GitHub job. `CHECKS.json` records the exact hashes, exports, controls and limitations.

The full Solution was freshly built. All 22 declarations were exported from separate Challenge and Solution environments and compared without definition holes. The Challenge's 22 specification placeholders were confined to its separate environment. Every Solution export reported only `propext`, `Classical.choice` and `Quot.sound`; the Solution accepted no `sorryAx` or native-decide axiom. LeanCert's kernel-trust assertions and the actually consumed arithmetic certificate compiled. The actual Comparator log records both `Lean default kernel accepts the solution` and `Your solution is okay!`, followed by exit status zero.

## Actual required rejection and sandbox controls

The extra workflow job named `checker-controls` was skipped because the shared harness was unchanged. This is not an omission of the project's required controls: the successful MF-22 verify job itself executed them before the full fresh verification:

- The genuine kernel accepted the honest inductive/quotient case, rejected an invalid raw proof, and rejected a quotient postcheck mismatch.
- All five Comparator regression cases produced their expected acceptance or rejection, covering statement, declaration-kind and forbidden-axiom mismatches.
- The deliberate `sorry` and `native_decide` projects were rejected with nonzero status and their actual forbidden axioms identified.
- Build and export sandboxes ran as UID 1001. Their required write restrictions, private namespaces, host isolation, socket/network denial, capability restrictions and invalid-policy controls passed.

Pinned Lean 4.33.1, all ten dependency revisions, checker/exporter binaries and the source-lock receipt were reconciled. The shared harness and workflow bytes remain unchanged from accepted revision `ff6abf718126ceb23f933cf4f627f95104461fe8`. This referee did not run Lean, Lake or a cache locally and did not modify the proof candidate.

## Mathematical and publication scope

The complete original MF-22 target is certified: for every fixed positive real parameter, the literal complex pure Toeplitz family is eventually nonsingular and its genuine Euclidean condition number has a polynomial bound. The formal result supplies exponent **two**. It does not claim the informal manuscript's stronger exponent-one estimate. The complete-source report explains the exact boundary, recurrence, spectral, Green-kernel and operator-norm correspondence.

This addendum supports preparation of publication metadata for the accepted proof. It does not assert an upstream PR, merge, later publication-commit run or updated verified count. Later revisions must be separately reconciled and checked. The result is an independent audit of one authenticated GitHub execution, not an independently executed second Lean run, external human peer review, formal verification of checker software, or a guarantee that GitHub and the tools are infallible.

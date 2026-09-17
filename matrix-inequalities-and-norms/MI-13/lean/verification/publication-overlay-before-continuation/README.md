# MI-13 Lean formalization

This formalization proves the original complex rectangular inequality

```
‖ABC − CBA‖F² ≤ 2 ‖B‖op² (σ₁(A)² + σ₂(A)²) ‖C‖F²
```

for every m,n ≥ 2, complex m-by-n A,C and n-by-m B. The norms are the actual Euclidean operator and Frobenius norms; the singular values are Mathlib's actual decreasing singular values. Zero matrices, deficient ranks, repeated values and both dimension orderings are included.

**Complete canonical Linux verification passed.** Actual [run 35191730986](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35191730986/job/105105676064) checked literal proof revision `e37310121f154b1a0d94efa4f98fdcd469177134`, all 1,183 submitted inputs and all 36 exact contracts. Default-kernel replay, Comparator, standard transitive axioms, kernel-mode LeanCert and the required rejection/isolation controls passed. [Retained logs and the coordinator audit](verification/linux-35191730986/README.md) bind that execution to the source. Later publication and upstream PR checkouts require separate records.

The earlier actual serial macOS run and exact successful reuse remain in [LOCAL-COMPLETE.json](verification/LOCAL-COMPLETE.json) and the [command origins](verification/local-development/COMMAND-ORIGINS.json). Two complete nonauthor proof reviews and the independent package review are accepted, with precise scopes in [reviews/INDEX.json](reviews/INDEX.json). Independent canonical runtime and publication-document reviews are pending for this private overlay. Evidence audits are not additional compiler executions. Historical inventories and frozen-handoff metadata retain their original stage wording; current status is in formalization.yaml and PUBLICATION-EVIDENCE.json.

Read the [numerical targets](NUMERICAL_TARGETS.md), [Definitions](NLA/MI13/Definitions.lean), independent [Challenge](Challenge.lean), [source correspondence](SourceCorrespondence.md) and [Solution](Solution.lean). Challenge contains deliberate specification holes and is never imported by the implementation. All 36 declarations are selected by [comparator.json](comparator.json), with no replaceable definitions. [IMPLEMENTATION-MAP.json](IMPLEMENTATION-MAP.json) gives their exact defining files.

The refined commutator bound is proved internally using the actual Hilbert–Schmidt commutator operator, a maximal eigenvalue, a two-vector eigenspace argument, and cancellation of one SVD coordinate. Every square contraction is the average of two unitaries. Actual block padding preserves both norms and all zero-extended singular values, yielding the rectangular theorem. Padding uses m+n rather than the informal proof's max(m,n), with the same coefficient. A genuine 2-by-2 example checks sharpness.

The only LeanCert interval calculation is the exact positive half certificate in kernel mode, consumed in Frobenius averaging. Matrix, spectral and variable scalar arguments are symbolic; there is no interval grid or numerical sampling. Direct pinned Mathlib lemmas are reused for the unit-circle lift.

The [freeze](STATEMENT-FREEZE.json) and historical reports retain their original preparatory wording. Later source code and runtime records do not rewrite that history. All mathematical frozen inputs are unchanged. The sole operational Lake change registers Solution and selects it as the default; the [diff](verification/packaging/LAKE-REGISTRATION.patch) and original file are retained. Inactive historical Lean copies have a .txt suffix and an explicit original-path/hash map.

With pinned dependencies available, run `lake build` in this directory. From the repository root, final Linux verification uses the shared [harness](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-13/lean /absolute/path/to/nla-lean-tools
```

Formalization contributor: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance is disclosed. Nobori's original problem, Audenaert's refined commutator theorem, the repository reduction, and Mathlib, LeanCert, Comparator, Schiffer and Forsythe contributions retain their attribution. Scoped AI-agent review is not official Tau Ceti endorsement or human peer review. [License](LICENSE).

# SF-01 resolvent prefix: independent source approval

Reviewer: `/root/mf22_publication_referee`, a nonauthor of SF-01. I author
unrelated MF-07 and RA-02 work. **Approve the exact four-module, 237-line
`resolvent-04` source prefix for a subsequent coordinated Linux build.** No
required mathematical or source-fidelity correction was found. This is source
review, not a successful Lean run, Comparator result or full SF-01 verification.

The approved author manifest is
`821ed1d6389bc95503b30f26d2f5917b3561b1baefd007b5f16ba828614ed304`, with complete
21-source closure
`da9b3f4cb6e338b9272c4a422cb67a667ea79c817bb145374c58f17ff9ac0c99`.

## Scope and semantic checks

I read all four new files, their complete prior statement plan, all 24 frozen
contracts, the shared definitions, and the original canonical page and full
retained manuscript at upstream `ce47b5630bf3680d9211131c3a43825b022c139a`.
I reconciled my earlier complete 13-source analytical-bridge review with this
21-source candidate: the four intervening spectral-converse files and the two
changed foundation files were read in full, as were the reused IV-03 maximum
principle and its SF-01 adapters. The unchanged earlier analytical proofs remain
bound to that prior full review. The four new public signatures exactly match
the frozen boundary. The original all-iteration Newton theorem remains pending.

The representation of an H-matrix still uses the actual complex spectral
radius of its comparison matrix. Positive weight is a derived property, not a
new input restriction. The intervening converse proves that a weighted Z-matrix
has the original spectral representation: its finite maximum-ratio bound uses
actual complex eigenvectors. The H-weight argument proves unitness by positive
column scaling and the existing strict diagonal-dominance determinant theorem.
These dependencies supply the hypotheses used by the new shift argument.

`ShiftStructure` preserves the exact diagonal/off-diagonal comparison identity
because the original diagonal is positive and the shift is nonnegative. The
shifted comparison matrix is Z and sends the same strictly positive weight to
the old positive image plus `t*v`. The proved converse therefore establishes
the spectral H predicate of the shifted matrix. Unitness and positive diagonal
are proved before any inverse-column equation is invoked. The endpoint `t=0`,
dimension one, and arbitrarily large nonnegative shifts are included.

`AbsoluteComparison` proves the stronger general real-matrix inequality
`comparison(A)*abs(y) <= abs(A*y)` without a sign condition on `y` or `A`.
It separates one diagonal row summand, bounds the absolute off-diagonal sum,
and applies the triangle inequality to that diagonal summand. The inequality
direction is correct: subtracting the sum of off-diagonal absolute products
can only lower the diagonal absolute product. The shifted frozen contract
then follows from the exact comparison identity. This introduces no entrywise
positivity assumption on the input matrix.

`ResolventDomination` proves both actual matrix unit obligations. For every
column, the exact nonsingular-inverse equations give `S*x=e_j` and `C*z=e_j`,
where `S=A+tI` and `C=comparison(A)+tI`. Absolute comparison yields
`C*abs(x) <= e_j`; subtraction gives `C*(z-abs(x)) >= 0`. The actual weighted
Z maximum principle then gives `z-abs(x) >= 0`, exactly the desired entrywise
inverse inequality. It does not infer order preservation from a formal or
possibly singular inverse. I checked the hypotheses and direction of the
unchanged, credited IV-03 maximum principle directly.

## Source, API and standards checks

My independent static audit rehashed all 15 new packet entries, all 113 author
binding records, all four predecessor inventories, the exact 21 candidate
sources, the nine frozen inputs and the 24-contract boundary. It checked that
all 17 new signatures equal the written preimplementation plan, all 12 public
contracts currently implemented in source match Challenge, and all local
imports stay within the stated candidate. The previous 17 candidate inputs
and original author-workspace bytes are unchanged. Numerical and
Complexification are deliberately taken from their two immutable repair
snapshots; their stale original workspace paths are not mistaken for candidate
inputs. The four new immutable snapshots equal their author-workspace files.

All seven cited primary API files were independently authenticated against
pinned Mathlib Git commit `0df444a360eaa60ab8c11dca51a86af692955474`, and the
actual finite-sum, triangle, matrix-vector and nonsingular-inverse signatures
were inspected. Targeted searches in the pinned matrix algebra/analysis/data
libraries did not locate a direct comparison-matrix resolvent theorem that
replaces this project-specific bridge. The standard row-splitting, inverse and
triangle APIs are used directly. This bounded search is not an exhaustive
library or unpublished-work audit.

The applicable Tau Ceti correctness, generality, proof-quality, reuse and
attribution rubrics were read and applied manually. I did not execute the Tau
Ceti CLI. The small literal row-sum and matrix-entry `change` steps identify the
existing matrix operations; they do not hide a different norm, spectrum or
predicate. The general absolute-comparison helper has an immediate consumer.
The remaining concrete helper wrappers are consumed in the frozen contracts.
No new abstract assumptions or theorem-bearing structures are introduced.

Sidney Holden's two unchanged Apache-2.0 IV-03 sources and their formalization
credit remain intact. Matthew J. Colbrook retains mathematical attribution;
George Stepaniants retains formalization credit with the Caltech Department of
Computing and Mathematical Sciences affiliation and AI-assistance disclosure.
No email was added to the new sources. No local Lean, Lake, cache, Git mutation,
CI dispatch, publication or status/count change was performed by this review.

## Limits and preparation history

The prior foundation run 35090376438 failed, and its repaired candidate is a
separate pending execution matter. These four new modules were not in that
run. `ResolventChecks` is an explicit partial-prefix wrapper: printed axiom and
kernel-trust commands are requests for a future execution, not receipts.
Twelve of the 24 full-problem contracts still lack source implementations.

Two initial attempts of my static review preparer stopped before producing
review outputs because historical inventories used different JSON field/value
formats. Their exact scripts and explanations are retained under
`preparation-history`. The corrected read-only reader passed 142 unique
external bindings. No author source or sealed evidence was edited to make a
check pass. These were audit-reader errors, not Lean execution failures or
mathematical repairs.

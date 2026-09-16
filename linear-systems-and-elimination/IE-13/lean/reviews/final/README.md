# IE-13 complete source and actual-runtime reviews

Two nonimplementing AI-agent referees approved the complete original target,
the 27-file mathematical graph and all 28 frozen contracts, including the
source-preserving repair chain. Their final runtime continuations are:

- [Matrix-functions referee](matrix-functions-runtime/REVIEW.md).
- [Inequalities referee](inequalities-runtime/REVIEW.md).

Both independently audited actual canonical run 35081003513 at literal commit
`032d4c86c52ffde0c4d440f28527ba43555a0a24`, rehashed all 95 tested inputs,
and read the full Comparator and required control logs. The [actual evidence](../../verification/linux-2026-09-16/README.md)
is retained without altering old records. Existing `reviews/source` reports
remain unchanged; selected additional complete-source, repair and packaging
reports and their original seals are retained in `history`.

[The inventory](RETAINED-REVIEWS.json) maps each copied record to its exact
original bytes. Their historical manifest/script paths refer to the original
private audit context. This is a bounded evidence copy, not a claim that every
large private archive is present or those historical scripts are portable.
Use the shared repository verification command to reproduce the proof check.

The scoped Tau Ceti protocol supplied fidelity and adversarial-review criteria.
These are AI-agent audits, not external human peer review or official Tau Ceti
endorsement. Semantic source review is separate from kernel/type acceptance.
Reviewing a run is not an independently executed second run, nor a proof of
checker/platform infallibility. After these reports were sealed, the
matrix-functions referee prepared publication metadata only. Root owns its
independent publication review, exact publication-head rerun and upstream PR.

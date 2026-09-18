# Independent final NM-04 mathematical and source review

**Verdict: approve the exact local187 proof source and all 35 frozen contracts.**
This is one complete canonical target, the Rowland–Wu coefficient identity
for every positive real rectangular matrix with both dimensions at least one.
It is not approval of an upstream commit, a GitHub run, or a completed campaign
count. Those publication and runtime gates remain separate.

Reviewer: `/root/nm04_final_referee1`. I have never authored an NM-04 statement,
Lean proof, helper implementation, repair, or compiler harness. I did not
change the candidate's Lean files. This independent agent review is not human
peer review or an official Tau Ceti service review. I read the earlier
referee1 findings to check their resolution, but did not read referee2's final
findings. My own conclusions were first recorded in
`INDEPENDENT-INITIAL-FINDINGS.json` before any such comparison.

## Exact review scope

I read the entire original canonical README and the entire retained Colbrook
manuscript, all concrete definitions, every Challenge type, and all 38 modules
in the final Solution import closure. `CONTRACT-REVIEW.json` records separate
substantive reasoning for each of the 35 statements. The mathematical target
is Theorem 1 and Sections 1–4 of the manuscript. Later arbitrary-margin,
exterior-power, symmetry and degree results in that manuscript are not claimed
to have been formalized here.

The source184 full read was followed by a complete inspection of the only
source184-to-source187 differences: explanatory comments in RankOneBordered
and SchurBordered. Exact equality after removing line-comment lines confirms
that these modifications changed no other source text. I inspected the new
local187 success logs as well. The approved source hashes are in VERDICT.json;
the original coordinator completion record is
`evidence/local/NM04-LOCAL-COMPLETE-187.json`, SHA256
`d32daefe49cde06358205c59a897a439f3af49aa8d017b31a68f8265893efa4d`.
All frozen mathematical inputs still match STATEMENT-FREEZE.json.

The original canonical page from Git commit
`849003686970b372e1b2128ba072f86168f81d38` and the observed current base
`3923b68ecee13d02e732085a57b42a2e7e95ac7a` are byte-identical. I actually
compared the retained files with `git show` for those exact objects, and
likewise checked the complete TeX source. This is a local Git-object check,
not a fresh network search of forks or an assertion about future upstream
changes. The retained primary page is not confused with the differently
formatted README copy in the older provisional review snapshot.

## Faithfulness and mathematical correctness

The final quantified inputs are precisely every natural m,n≥1 and every
strictly positive real m-by-n matrix. There is no hidden bound on dimensions,
genericity assumption, nonzero-minor condition, rank hypothesis, supplied
scaling witness or assumption of the desired identity.

The canonical README explicitly defines its Sinkhorn matrix equivalently as
the unique positive diagonal scaling with row sums one and column sums m/n.
The formalization adopts that exact characterization. The total `sinkhorn`
choice has a fallback only on inputs for which no such scaling exists. A
complete internally proved existence theorem excludes that fallback on every
input covered by the target, and matrix uniqueness proves that the chosen
object is the required one. No convergence theorem for alternating row and
column normalization is claimed or needed for this explicit equivalent
canonical definition.

The analytic existence proof uses actual finite exp/log expressions. It
proves positivity of row partitions, continuity, and the real directional
derivative of the log-partition potential. On the mean-zero hyperplane, a
largest coordinate q is nonnegative, and the deficits q−t_j control the
finite-product sup norm by n q. A positive lower bound on the finitely many
matrix entries supplies a logarithmic lower bound for every row. Coercivity
makes a sublevel compact, and the extreme value theorem gives a genuine
global constrained minimum. The imbalance vector itself has coordinate sum
zero; applying the proved derivative along that vector identifies a sum of
squares, which vanishes at the minimum. The resulting exponential and
reciprocal-partition factors verify both margins. Matrix uniqueness follows
from equality in positive weighted sums at a maximum column factor. The
legitimate reciprocal scalar gauge in the factors remains unrestricted.

The use of compact sublevels and the imbalance direction improves the
original prose plan without changing any frozen statement. It does not turn
minimization or stationarity into an assumed structure field. Both strict
half inequalities are proved by kernel-mode LeanCert and actually consumed
in coercivity; positivity is also consumed in the minimizer construction.
All dimension-dependent estimates are symbolic. No interval grid, numerical
Sinkhorn iteration, floating-point matrix, or fixed-size determinant search
is a premise.

Minor indices are actual equal-cardinality finite subsets of exactly the
tail labels. The increasing order embeddings are not arbitrary enumerations.
`position` is one plus the number of smaller selected elements, and its
semantics is separately proved. The diagonal of H uses integer subtraction.
Unique singleton differences and disjoint supports give exactly the four
off-diagonal patterns with weights m, −n, m, n and precisely the source's
signs. Every unsupported off-diagonal entry vanishes. Equality-decision
transports use subsingleton equality only; they do not change any finite
enumeration, matrix value or mathematical assumption.

The cofactor form is an explicit adjugate sum. The signed erased-minor
formula follows from the existing adjugate theorem and actual order
embeddings. Universal alternating multilinearity proves rank-one updates
over arbitrary commutative rings, killing terms with two proportional rows.
The bordered identity uses an invertible scalar unit corner and affine
dependence on its last entry; it never inverts the selected minor. Column
replacement separates the original selected column, repeated selected
columns and genuinely new columns. Its sorted signs are proved through
matching Laplace expansions. Row exchange reuses that proof by actual
transposition. The raising identity sums universal bordered determinants
over all ambient row and column pairs, discards only genuinely repeated
borders, and derives the insertion signs from finite permutations.

For an empty minor the cofactor sums are empty, the determinant is one, and
the raising identity reads 0 = sum(T) − sum(T). The generic ring statements
also cover singular leading blocks. Positivity is only needed in the
balanced Schur construction to invert the distinguished first entry. Its
three actual margin identities and rank-one reconstruction give the full
master minor relation. The cardinality weights turn raising m into n and
lowering −n into −m. The null vector's empty coordinate equals one, so it
cannot be a vacuous zero witness.

Both delta and gamma acquire the identical row/column covariance factor.
For positive scaling factors the transported null vector has a strictly
positive empty coordinate. The principal-minor expansion is universal even
with zero diagonal weights or an empty index type. Applying it to m⁻¹H
produces exactly det(m⁻¹H_E), the delta product over E, the gamma product over
its complement and the actual Sinkhorn first entry to the power |E|. It is
not a merely generic determinant-zero or algebraic-degree surrogate.

All positive rank-one inputs and all other vanishing-minor patterns are
included. When m=1 or n=1, the tail minor index still contains its empty
pair, H has the single value −mn, and the formula reduces to
a₁₁(1−n x)=0 with x=1/n. The one-by-one case is included. A specialization
may be the zero polynomial; the unchanged canonical problem asks for the
coefficient identity and does not demand polynomial nontriviality.

## Closure of the previous review findings

- **F01 closed:** Solution imports TransitionEntries explicitly as well as
  Canonical. The actual complete closure has 38 modules, and every C13–C18
  export occurs in the final successful Solution log.
- **F02 closed:** DecisionTransport contains the single shared support and
  coefficient transports. TransitionEntries, ColumnExchangeIndices and
  WeightedTransition reuse those definitions. No duplicate families remain.
- **F03 closed:** MinorBasics now owns `minor_ordered_det` and
  `position_ordered_card`. CofactorSigned, MinorTranspose and BorderOrder
  reuse these exact shared bridges instead of redeclaring them.
- **F04 closed for the requested wrapper bridges:** WeightedExpansion
  explains its alternating-map, principal-submatrix and transpose bridges.
  RankOneBordered explains the row-function, Cramer, block-index and
  selected-rank-one-entry bridges. This continuation identified the remaining
  undocumented Schur block/pivot bridges; the comment187 patch explains
  them, including why no tail-minor inverse occurs. The remaining short
  definitional changes expose the concrete objects already specified in
  their nearby lemma documentation; they do not assert undocumented
  mathematical equalities across different indexings.
- **F05 closed:** The unused frozen `hn` binder is retained and explained in
  WeightedTransition. `clear hn` was removed. The ordinary linter warning is
  retained in the actual successful origin log, not suppressed or concealed.

## Tau Ceti standards, reuse and attribution

I applied the retained pinned correctness, reuse, proof-quality, generality
and attribution rubrics directly. I did not invoke the Tau Ceti review
service/engine, and no official endorsement or exhaustive search of a
separate Tau Ceti theorem library is claimed.

I ran and read six groups of bounded primary-source searches in the pinned
Mathlib checkout. Commands and raw outputs are retained, and nine relevant
primary Mathlib files were matched byte-for-byte to Git revision
`0df444a360eaa60ab8c11dca51a86af692955474`. The searches cover scaling,
minima, derivatives, adjugates, rank-one and bordered determinants,
multilinearity, principal minors, ordered enumeration and permutation signs.
No located declaration directly replaces a new complete theorem here.
The existing `det_add_replicateCol_mul_replicateRow` requires `IsUnit A.det`
and explicitly lists the singular adjugate version as a TODO. Bird's
`det_bordered_expand` uses a same-label square principal-minor setup and
expresses another Laplace expansion, not the needed universal arbitrary
rectangular-set adjugate formula. The finite-complement singleton enumeration
lemma concerns the special ambient `Fin (n+1)` case; the erased selected-set
bridge here legitimately uses the existing general order-embedding
uniqueness API.

The development genuinely reuses the existing alternating multilinearity,
Cramer/adjugate, principal-minor, determinant scaling, order-embedding,
permutation, compactness and Fermat APIs. Generic algebra is proved over
commutative rings and row exchange reuses column exchange by transposition.
The real assumptions are restricted to the actual analytic and positive
scaling parts. The Schiffer and Forsythe examples were read for concrete
statement boundaries and independent Challenge structure; no mathematical
theorem from either project is imported or reassigned.

The code credits George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, for formalization, with
substantial OpenAI Codex assistance. It preserves Rowland and Wu's question
and Matthew J. Colbrook's mathematical solution, and acknowledges the
libraries and workflow sources. No email for George Stepaniants occurs in
the reviewed candidate. The retained original TeX includes its original
author's contact information; that is not the user's email.

## Execution evidence and publication limitations

I ran no Lean, Lake, Comparator, default-kernel replay, Linux sandbox or
GitHub job. I inspected the coordinator's actual successful origin logs for
all 38 modules at local184, followed by all seven fresh local187 logs and
the final 35-export axiom report. The successful local187 run consists of
seven freshly compiled changed/dependent modules and 31 reused successful
outputs whose local source, transitive local dependency and output hashes
are bound through retained receipts. Those categories remain distinct.
The actual commands specify one thread and a 4096 MiB cap, and the serial
driver runs one compiler at a time. Every final exported theorem reports
only propext, Classical.choice and Quot.sound and passes the source's kernel
trust assertion. The final source closure does not import Challenge.

I read the evidence verifiers before using them. I actually executed the
old provisional packet's read-only verifier and retained its PASS result
with 473 consistency checks; this does not approve that old failed source.
The new `verify_review.py` checks this final packet's complete source
closure, frozen headers, actual receipt/log chains, axiom reports and review
scope. It explicitly does not execute a compiler or certify that logs are
unforgeable. Independent exact-commit Linux Comparator/default-kernel/
sandbox/rejection-control checks remain required before a final campaign
acceptance claim.

The local187 publication package is a separate mutable preparation area.
I checked its mathematical-source hashes against the approved source and
its metadata's candid separation between local success, final agent review
and unrun Linux checks. Frozen statement-stage documents deliberately retain
their historical draft wording. The package now supplies the referenced
precode-01 and SEMANTIC-PLAN historical files without rewriting those frozen
documents. Root is responsible for final archive/schema checks, exact
published commit/run binding, upstream PR creation and any canonical status
promotion. This review does not authorize claiming those future steps have
already succeeded.

There is no remaining mathematical or proof-source blocker in the approved
local187 bytes. A later mathematical/source change must be reviewed again;
this approval does not automatically transfer to a different version.

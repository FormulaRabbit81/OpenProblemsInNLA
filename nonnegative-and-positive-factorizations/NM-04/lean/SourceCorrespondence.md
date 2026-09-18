# NM-04 source correspondence and exact statement boundary

Status: unreviewed, unelaborated **statement draft**. This is an author’s mapping,
not an independent review or proof acceptance. `STATEMENT-HEADERS.json` retains
the exact text of every proposed type, and `comparator.json` lists exactly the
same 35 theorem names, with no definition holes. The declarations below have
intentional `sorry` bodies only in Challenge.

The immutable primary target is upstream commit
`849003686970b372e1b2128ba072f86168f81d38`, canonical path
`nonnegative-and-positive-factorizations/NM-04/README.md`. The original complete
solution is Matthew J. Colbrook’s **A null vector for the Rowland–Wu determinant
identity**, Theorem 1, Sections 1–4, at
`references/colbrook-factorization-2026-09-11/manuscripts/NM-04_sinkhorn_identity.tex`.
Its entire retained source SHA256 is
`cc794d1fe11d5ae3bc5eaf1a635720ed0ad5c977cba4c7c7064dc7f29bff0c8f`.
Original question attribution remains Eric Rowland and Jason Wu.

## Every proposed contract

| ID | Actual Challenge declaration | Mathematical source or role |
|---|---|---|
| C01 | [`coercivity_half_certificate`](Challenge.lean#L24) | New exact rational certificate, consumed by the scaling existence argument. |
| C02 | [`row_partition_positive`](Challenge.lean#L28) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C03 | [`potential_continuous`](Challenge.lean#L33) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C04 | [`potential_line_derivative`](Challenge.lean#L38) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C05 | [`zero_mean_coercivity`](Challenge.lean#L45) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C06 | [`potential_attains_minimum`](Challenge.lean#L52) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C07 | [`potential_minimum_has_margins`](Challenge.lean#L58) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C08 | [`positive_balanced_scaling_exists`](Challenge.lean#L65) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C09 | [`positive_balanced_scaling_unique`](Challenge.lean#L70) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C10 | [`sinkhorn_semantics`](Challenge.lean#L76) | Canonical README’s equivalent positive-scaling definition; prerequisites supplied internally by finite-dimensional minimization and matrix uniqueness. |
| C11 | [`position_sorted_semantics`](Challenge.lean#L82) | Canonical README’s increasing order, one-based positions and empty-minor conventions; manuscript Section 1. |
| C12 | [`empty_minor_values`](Challenge.lean#L87) | Canonical README’s increasing order, one-based positions and empty-minor conventions; manuscript Section 1. |
| C13 | [`H_diagonal`](Challenge.lean#L94) | Canonical README’s entire piecewise integer H formula; manuscript Section 1. |
| C14 | [`H_raising`](Challenge.lean#L98) | Canonical README’s entire piecewise integer H formula; manuscript Section 1. |
| C15 | [`H_lowering`](Challenge.lean#L103) | Canonical README’s entire piecewise integer H formula; manuscript Section 1. |
| C16 | [`H_column_exchange`](Challenge.lean#L108) | Canonical README’s entire piecewise integer H formula; manuscript Section 1. |
| C17 | [`H_row_exchange`](Challenge.lean#L113) | Canonical README’s entire piecewise integer H formula; manuscript Section 1. |
| C18 | [`H_other`](Challenge.lean#L118) | Canonical README’s entire piecewise integer H formula; manuscript Section 1. |
| C19 | [`weighted_principal_minor_expansion`](Challenge.lean#L126) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C20 | [`cofactor_signed_minor_formula`](Challenge.lean#L134) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C21 | [`universal_rank_one_update`](Challenge.lean#L144) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C22 | [`universal_bordered_determinant`](Challenge.lean#L151) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C23 | [`minor_lowering_identity`](Challenge.lean#L157) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C24 | [`minor_column_exchange_identity`](Challenge.lean#L163) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C25 | [`minor_row_exchange_identity`](Challenge.lean#L170) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C26 | [`minor_raising_identity`](Challenge.lean#L177) | Manuscript Section 1 determinant reformulation and Section 2 four elementary identities; universal algebraic prerequisites. |
| C27 | [`schur_margin_identities`](Challenge.lean#L185) | Manuscript Section 3 Schur-complement equations, master minor relation and explicit null vector. |
| C28 | [`schur_bordered_minor`](Challenge.lean#L196) | Manuscript Section 3 Schur-complement equations, master minor relation and explicit null vector. |
| C29 | [`balanced_minor_relation`](Challenge.lean#L201) | Manuscript Section 3 Schur-complement equations, master minor relation and explicit null vector. |
| C30 | [`weighted_transition_action`](Challenge.lean#L210) | Manuscript Section 3 Schur-complement equations, master minor relation and explicit null vector. |
| C31 | [`balanced_null_vector`](Challenge.lean#L219) | Manuscript Section 3 Schur-complement equations, master minor relation and explicit null vector. |
| C32 | [`diagonal_minor_covariance`](Challenge.lean#L225) | Manuscript Section 4 identical diagonal covariance of Δ and Γ and the pencil. |
| C33 | [`diagonal_pencil_covariance`](Challenge.lean#L231) | Manuscript Section 4 identical diagonal covariance of Δ and Γ and the pencil. |
| C34 | [`sinkhorn_pencil_singular`](Challenge.lean#L237) | Manuscript Theorem 1 and the complete original canonical identity, all m,n≥1 and all positive real A. |
| C35 | [`rowland_wu_identity`](Challenge.lean#L244) | Manuscript Theorem 1 and the complete original canonical identity, all m,n≥1 and all positive real A. |

The complete propositions—not only these role labels—are displayed in
Challenge, and the original planned propositions are retained in
`precode-01/CONTRACT-PLAN.json`.

## Concrete semantic correspondence

- `Rect m n` is an actual real matrix on `Fin m` and `Fin n`. Public final
  hypotheses `1≤m` and `1≤n` include every canonical dimension. `Tail m`
  contains exactly the positive zero-based indices, corresponding to the
  source labels 2 through m, and is empty when m=1.
- `MinorIndex` is an actual finite pair of equal-cardinality subsets. Sorted
  submatrix entries use `Finset.orderEmbOfFin` and ordinary `Matrix.det`.
  `delta` prepends the first index to the increasing tail indices, while
  `gamma` multiplies the first matrix entry by the actual tail minor.
- `position` counts smaller members plus one. Four literal set-difference
  support predicates determine signed transition coefficients. `H` combines
  them with weights m, −n, m, n, and its diagonal subtraction is in integers.
  C13–C18 require the exact canonical case formulas, including all other
  entries being zero. These are not empirically fitted coefficients.
- The principal submatrix in C35 is indexed by the subtype of each finite
  subset E, and is scaled by the real inverse of m before its determinant.
  The full finite sum includes every subset, with the product of Γ over the
  complement and the exact power `E.card`. Simultaneous row/column reindexing
  uses Mathlib’s standard determinant invariance.
- `sinkhorn` is a conditional classical choice from the concrete predicate
  `ScaledBalanced`, with zero fallback only when no witness exists. C08–C10
  must prove witness existence, matrix uniqueness, positivity, and that this
  choice is the canonical scaled matrix. The final contract has no supplied
  scaling oracle or balancing witness in its assumptions.
- `rowPartition`, `potential` and `columnImbalance` are explicit exp/log and
  finite-sum expressions. C04 requires their actual derivative; C06 requires
  an actual attained minimum on the mean-zero hyperplane. Those properties
  are not definition fields. The coefficient of the sup-norm coercivity
  bound consumes the two kernel-mode rational half inequalities.
- `cofactorForm` uses the actual adjugate, with ordinary finite summation;
  the relation to signed deleted minors is C20. C21 and C22 are universal
  rank-one and bordered identities over arbitrary commutative rings. They
  cannot be replaced by Mathlib’s invertibility-restricted Schur-complement
  rank-one lemma. Empty and singular selected matrices are included.
- `schurTail` divides only by the distinguished first entry, with nonzero
  pivot proved from positivity where needed. C29 contains all four signed
  minor sums; C30 connects them to the literal H and the weight `(n/m)^k`.
  C34 requires a strictly positive empty coordinate in a genuine null vector,
  preventing a trivial zero-witness claim.

## Scope-preserving differences from the initial prose plan

The final target is unchanged. The actual draft uses weaker prerequisites
where the chosen APIs have them: C11’s finite set can lie in an arbitrary
linearly ordered ambient type; C20/C21 do not require finite ambient types
because only their chosen finite minors occur. C02–C05 and C07 also allow
m=0; their universal formulas do not need a positive number of rows. C05’s
positive lower bound implies entrywise positivity, so that redundant
hypothesis was removed. The full scaling existence and the canonical result
retain m,n≥1. The exchange coefficient definitions ask only for an order on
the index type whose positions are used, and a decidable equality on the other.
Pure algebra is formulated at the natural commutative-ring level, then used
over ℝ. No matrix-size restriction was introduced to reduce computation.

The canonical page explicitly equates the Sinkhorn limit with the unique
positive diagonal scaling having the prescribed margins. This is the adopted
concrete definition. No alternating-normalization convergence theorem is
claimed. The source’s later arbitrary-margin, exterior-power and coefficient
symmetry results are outside the configured contracts.

## Evidence and review boundaries

The first prose plan suggested separate review rounds for prose and code.
The coordinator subsequently authorized these statement-only files and
clarified that two independent approvals should review the actual complete
Definitions and Challenge before proof implementation. This is the current
gate; the sealed historical plan is retained unchanged.

No `.olean` result, local Lean invocation, kernel certificate, final axiom
report, independent approval or Comparator run has been produced for NM-04
by this preparer. A Python header/integrity/schema check is only a source and
packaging check. The initial statement draft is not a statement freeze.

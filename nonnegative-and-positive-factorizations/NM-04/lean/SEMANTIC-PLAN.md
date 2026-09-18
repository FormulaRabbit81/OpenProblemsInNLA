# NM-04 concrete definitions and proof boundary

Status: **pre-code review requested**. This document proposes definitions and
contracts; it is not a Lean elaboration report. The complete numerical and
mathematical propositions are in `NUMERICAL_TARGETS.md`. Primary source hashes
and pins are in `SOURCE-BINDINGS.json`.

## Representation decisions

1. Public matrix dimensions remain `m n : ℕ` with explicit hypotheses
   `hm : 1 ≤ m`, `hn : 1 ≤ n`. The public matrix is
   `Matrix (Fin m) (Fin n) ℝ`. The first index is `⟨0,hm⟩` or `⟨0,hn⟩`.
   This is zero-based storage of the original one-based indices.
2. Define `Tail m := {i : Fin m // 0 < i.val}`. Its increasing order is
   inherited from `Fin m`; the source's label is `i.val+1`. In particular,
   `Tail 1` is empty. This avoids an unnecessary reindex through `Fin (m-1)`
   and does not restrict any public dimension.
3. For arbitrary finite linearly ordered types `α,β`, define `MinorIndex α β`
   as the subtype of pairs `R : Finset α`, `C : Finset β` satisfying
   `R.card=C.card`. It has the existing finite-subtype infrastructure, with
   no `Nonempty α` or `Nonempty β` assumption. The canonical `D` is
   `MinorIndex (Tail m) (Tail n)`. Its empty pair is a concrete distinguished
   element for all dimensions.
4. The generic sorted minor of `T : Matrix α β ℝ` is a determinant over
   `Fin R.card`. Its row map is `R.orderEmbOfFin rfl`; its column map is
   `C.orderEmbOfFin h.symm` for `h : R.card=C.card`. This is ordinary
   `Matrix.det`, not a symbolic placeholder. The selected cardinality and
   sorted enumeration have no arbitrary permutations hidden in them.
5. Define the tail matrix by restricting `A` to the values of `Tail m` and
   `Tail n`. `Γ_A(I)=a₁₁*minor(tail A,I)`. For `Δ_A(I)`, form a square
   `(k+1)×(k+1)` matrix with `Fin.cons first (sorted tail indices)` as both
   index maps, and take its determinant. First-then-sorted-tail is exactly
   the increasing order of `{1}∪R` and `{1}∪C`; prove or reuse the relevant
   sorted-enumeration lemma rather than relying on undocumented definitional
   equality. Empty tails produce a genuine `1×1` determinant.
6. `pos s U = (U.filter (fun t => t<s)).card+1`. Prove it agrees with
   one-based `orderEmbOfFin` positions for members. The value on nonmembers
   is irrelevant to the four support predicates and will never justify a
   transition.
7. Define four **integer** transition coefficient matrices by finite sums of
   signed indicators for the four literal set-difference supports. A support
   has at most one pair of singleton witnesses. Up and down coefficients
   use `(-1)^(rowpos+colpos)`; the down coefficient is multiplied by `-n`
   in `H`, giving exactly the canonical exponent `+1`. Column and row
   exchange coefficients use the original and replaced set positions. The
   sums range over the actual finite row or column types, so empty types
   cause empty sums, not a chosen default index. The six contracts
   `H_diagonal`, `H_raising`, `H_lowering`, `H_column_exchange`,
   `H_row_exchange`, and `H_other` must establish the exact canonical
   piecewise formula, including uniqueness and disjointness of cases.
8. `H I J` is the diagonal entry when `I=J`; otherwise it is
   `m*up - n*down + m*columnExchange + n*rowExchange`, all in `ℤ`.
   Let `HReal` be its entrywise real cast. The four generic real minor-array
   operators use these same signed coefficients, without the dimension
   weights. This factors reusable transition data without hiding signs in
   an opaque action or supplying algebraic laws as assumptions.
9. The pencil is the actual matrix
   `Matrix.diagonal Γ + (z/(m:ℝ)) • (HReal * Matrix.diagonal Δ)`.
   The scalar polynomial expression is the literal finite sum over all
   `E : Finset D`, using `(HReal.submatrix Subtype.val Subtype.val)` on the
   subtype `E` and scalar multiplication by `(m:ℝ)⁻¹` **before** its
   determinant. This preserves every power of `m` in the coefficient.
   Use Mathlib's determinant reindexing theorem for enumeration independence;
   do not add an unnecessary forwarding theorem solely renaming that API.
10. `Positive A := ∀ i j, 0<A i j` and `Balanced S` is exactly the two finite
    margin equalities. `ScaledBalanced A S` is the concrete assertion
    `∃α β, (∀i,0<α i) ∧ (∀j,0<β j) ∧
      S=(fun i j =>α i*A i j*β j) ∧ Balanced S`.
    Define total `sinkhorn A` using classical choice of a matrix satisfying
    this predicate when one exists, and `0` otherwise. This total definition
    does not assert that a witness exists. The public existence and
    uniqueness contracts must prove that the fallback is never used on the
    canonical positive inputs and that the choice equals every such scaling.
11. The concrete row partition, potential, gradient, mean-zero set,
    row-normalized scaling, cofactor form, Schur complement, and weight
    vector have the formulas in `NUMERICAL_TARGETS.md`. No structure field
    assumes a minimizer, derivative, minor identity, null vector, scaling
    theorem, or final root identity.

## Comparator and independent statement process

The intended source boundary is `NLA/NM04/Definitions.lean`, importing only
pinned library definitions, and independent `Challenge.lean`, importing only
the definitions. Comparator's theorem list will contain the contracts in
`CONTRACT-PLAN.json`. Every Challenge proof body is an explicitly documented
statement placeholder; there are **no definition holes**. `definition_names`
is empty because definitions are concrete and frozen, not supplied by the
solution. Comparator checks the declarations used in the theorem types
between its independently built environments.

No solution module may import `Challenge`. Later proof modules will import
the definitions and libraries, provide every listed theorem with its exact
frozen type, and expose only the solution entrypoint to the proof build.
Every listed theorem will have actual `#print axioms` and kernel trust checks.
Only `propext`, `Quot.sound`, and `Classical.choice` may remain as axioms.

The present gate is review of these exact propositions by two independent
nonauthor reviewers. That permits drafting the concrete definitions and
independent Challenge, not proof implementation. A second concrete-source
review and the root's authorized serial local statement elaboration precede
the final statement freeze. Review scope must cover the whole final target,
the scaling prerequisites, every definition and every contract. Acceptance
of a route or a foundational lemma is not full target acceptance.

The frozen files will include Definitions, Challenge, contract list,
numerical targets, dependency pins, and source/metadata mappings. If a
mathematical contract changes later, preserve the old version and get two
new source-bound reviews before renewing the freeze. No proof-quality or
packaging cleanup may silently alter the final target.

## Planned library reuse and minimization

The pure determinant, cofactor and transition identities have no division or
order assumptions on their scalar ring. At the natural library level, their
contracts are therefore proposed over an arbitrary commutative ring, and are
specialized to `ℝ` for the canonical proof. This modest generalization has
immediate consumers; it introduces no new mathematical target or unsupported
claim about a noncommutative determinant.

- `Finset.orderEmbOfFin`, its membership/range properties, and inherited
  subtype orders implement the actual sorted minors. Reuse cardinality and
  insertion/deletion APIs rather than proving custom finite-list machinery.
- Use actual `Real.hasDerivAt_exp`, `HasDerivAt.log`, finite-sum derivatives,
  compactness of finite-dimensional closed balls, and
  `IsCompact.exists_isMinOn`. The minimizer argument does not assume a
  Sinkhorn, fixed-point, strict-convexity, or Lagrange-multiplier oracle.
- The elementary maximum proof of scaling uniqueness avoids an unnecessary
  separate strict convexity development or gauge uniqueness theorem.
- Reuse `Matrix.detRowAlternating.map_add_univ`,
  `Matrix.det_piecewise_one_eq_submatrix_det`, determinant row/column scalar
  rules, and `Matrix.det_submatrix_equiv_self` for the general weighted
  principal-minor expansion. Its source template is pinned Mathlib's
  `coeff_det_one_add_X_smul_eq_sum_minors`; arbitrary diagonal weights,
  including zeros, still need a proof. Do not divide by those weights.
- Reuse cofactor/adjugate lemmas and alternating multilinearity for the
  universal rank-one and bordered identities. The pinned
  `SchurComplement.lean:423` TODO explicitly confirms that its current
  `det_add_replicateCol_mul_replicateRow` assumes an invertible determinant.
  That result cannot discharge the required singular-minor contract.
- Use the actual scalar Schur pivot `x>0`; it is legitimate to invert this
  single entry. Reuse the scalar/block determinant lemma at that pivot.
- All dimension-dependent matrix/minor calculations stay symbolic. Do not
  expand a determinant by permutations at each size, enumerate numerical
  matrices, or attach a large interval certificate to an exact algebraic
  identity. The only interval work is the consumed rational half bound.

These are source-level reuse decisions, not claims that any indicated API
has already elaborated against NM-04 code. The pinned primary files are
preserved, and unsuccessful search scope is documented in the triage packet.

## Publication and attribution plan

After actual proofs pass locally, two independent full proof reviews and
the exact-source checks must precede publication. Root alone runs the local
compiler with one thread and a 4096 MiB limit. Other agents can work on
different source modules or review independently, without starting compilers.

The per-problem package will live at the unchanged canonical path
`nonnegative-and-positive-factorizations/NM-04/lean`. It will be a separate
PR to `ajt60gaibb/OpenProblemsInNLA:main`. Preserve the existing solved
status and Matthew Colbrook's mathematical authorship; add George's named
departmental Caltech formalization contribution. Do not publish George's
email. The exact inherited mathematical manuscript includes Colbrook's
already public author preamble; this local source snapshot is not a claim
that every copied source is email-free. Any published excerpt or archival
copy must accurately describe its relationship to the original bytes.

Add truthful schema-v0.4 `formalization.yaml`: the canonical question and
Colbrook solution are separate bibliographic sources, formalization author
George and AI assistance are distinguished, and theorem mappings name the
exact source Theorem 1 and mathematical prerequisites. Record limitations
and statuses; never mark this pre-code plan as a complete formalization.

Read patterns: Schiffer's exact domain/object definitions and independent
Challenge; Forsythe's separate shared definitions/Challenge, exact rational
numerical target document and full-target mapping. These are structural
influences, not imported Schiffer/Forsythe mathematics. The retained source
snapshots and provenance are bound in `SOURCE-BINDINGS.json`.

Apply the pinned Tau Ceti correctness, generality, proof-quality, reuse and
attribution rubrics to the actual source. This does not claim that the Tau
Ceti hosted service or reviewer CLI has been run. Fresh reviewers must try
to break all statements and must report exact source-bound scopes.

Final Comparator uses GitHub's actual non-root Linux runner and the accepted
campaign sandbox/kernel harness. No fake-landrun path, local macOS wrapper,
or unrun CI result will be called a Comparator success. The root checks the
changed-project selection before pushing to avoid unrelated all-project
workflows, and records exact commit, run ID, source hashes, logs and verdict.

## Present status and allowed next step

Only primary source acquisition and this mathematical pre-code plan exist.
All checks about Lean, LeanCert execution, statement elaboration, independent
acceptance, kernel proof, and Comparator remain **not run / pending**. The
preparer may draft concrete Definitions and Challenge after two accepted
pre-code reviews and root authorization. No proof implementation is included
in the present task.

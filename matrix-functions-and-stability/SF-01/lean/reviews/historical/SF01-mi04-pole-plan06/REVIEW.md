# Independent SF-01 pole-plan statement review

**Approve the exact fifteen proposed statements and mathematical route for
implementation.** No required correction was found. This is a preimplementation
review, not Lean elaboration, proof acceptance or a complete SF-01 verification.
Reviewer `/root/mi04_independent_referee` did not author this SF-01 plan or its
proof sources.

The reviewed author manifest is
`f18332a0cae17c737a4a85b7a0e1de3ea58ca2440bd94ad14e195d92a1b69a8b`,
and the plan text hash is
`9fbdde0403af33a32d02f13e7d0adaea0f6e789ae4f3f0ab900b180638c61265`.
I read the whole plan, all fifteen declaration signatures, the frozen ridge,
pole, spectral-coordinate and reciprocal-weight definitions, all four public
contracts in their full Challenge context, and the relevant primary API ranges.
This bounded review continues my previously sealed 25-source SF-01 review;
it does not repeat or claim a new audit of all historical runtime archives.

The four public statements exactly preserve the frozen
`pole_positive_definite`, `pole_diagonalization_exists`,
`pole_residue_normalization`, and `reciprocal_weights_nonnegative` contracts.
The other eleven statements are conclusions to prove, not extra assumptions
on the original Newton iteration. The unchanged definitions contain the actual
finite matrices and rational coefficients; no target conclusion is embedded
as data or a new predicate premise.

Write `u=poleVector d`, `D=diag(0,poles)` and `P=D+b⁻¹uuᵀ`. Expanding the
actual finite real quadratic form gives the stated sum of weighted squares.
Hermitianness holds even without ValidData because all coefficients are real
and the rank-one matrix is symmetric. Under ValidData, every ordinary summand
is nonnegative and its positive pole coefficient makes it strictly positive
when that coordinate is nonzero. If all ordinary coordinates vanish, a nonzero
vector has nonzero zeroth coordinate; `u₀=√a>0` and `b⁻¹>0` make the rank-one
term strictly positive. This proves the genuine Mathlib PosDef predicate,
including its Hermitian condition. The finite dot-product introduction API
has exactly the required meaning over the reals.

The real Hermitian spectral theorem and positive-definite eigenvalue theorem
then supply a genuine orthogonal matrix and strictly positive eigenvalues.
Both orthogonality identities are required and available from the unitary
matrix. Real conjugate transpose is transpose. No ordering, simple spectrum,
choice of a particular eigenvector, approximate spectrum or numerical
diagonalization is assumed. The proposed use of opaque matrix-level APIs also
avoids unnecessary expansion of the eigenbasis construction.

For normalization, `v=e₀ b/√a` is legitimate because ValidData proves both
denominators nonzero. The exact first column gives `P v=u`, and the single
coordinate dot product gives `uᵀv=b`. Under any supplied PoleDiagonalization,
putting `c=Qᵀu` and `y=Qᵀv` yields `lamᵢ yᵢ=cᵢ`; positivity of each eigenvalue
justifies `cᵢ²/lamᵢ=cᵢ yᵢ`. The other orthogonality identity preserves the dot
product, producing the exact sum b. This establishes the normalization for
every supplied diagonalization, not merely the one selected by the existence
theorem. Factoring out b⁻² then gives the additional weight-sum identity b⁻¹.
No block inverse or later reciprocal identity is used circularly.

The nonnegativity contract deliberately lacks ValidData. Its numerator is a
square and its denominator is `b² lamᵢ≥0`; real totalized division preserves
the desired weak inequality even when b=0. No positivity or invertibility
premise may be added to that header. Zero weights, repeated poles/eigenvalues,
an empty pole family and the one-dimensional pole matrix are all covered.
In the empty-family case P is the one-by-one positive matrix a/b. The general
orthogonal-dot helper also remains true for an empty index type. No proof
divides by a residue weight or its square root.

The pole dimension is determined solely by the scalar data. Choosing its
diagonalization does not introduce dependence on the original matrix A or its
dimension, so the later uniform Newton data-step quantifier order remains
available. That data step, the block unitness and reciprocal identity, first
iterate, uniform representation and final preservation theorem are still six
unimplemented public obligations after this proposed prefix. They are not
proved by approving this plan.

The independent static audit passes 138 checks: all eight plan-packet files,
69 retained external bindings, all 25 candidate/source locations and original
workspace bytes, nine frozen files, all 24 contract bytes, exact fifteen
planned signatures and four public matches. Ten complete primary Mathlib files
are authenticated to literal revision
`0df444a360eaa60ab8c11dca51a86af692955474`; the relevant positive-definite,
spectral, orthogonality, finite-sum, matrix-action and square-root API ranges
were read. The new modules were absent when checked. The local audit's first
attempt used a literal single-line affiliation match; normalizing whitespace
fixed that audit-only line-wrap check before the final pass. No author text
was changed.

The plan uses symbolic finite sums and fixed-size scalar identities, with no
new interval computation or theorem resource override. The existing consumed
LeanCert half certificate remains in the earlier source graph. George
Stepaniants's Caltech department/university formalization credit, Colbrook's
mathematical credit and Holden's attributed IV-03 reuse remain distinct; no
contact information is added. The relevant Tau Ceti fidelity, noncircularity,
edge-case, reuse and proof-boundary criteria are satisfied at statement level.

I ran no Lean, Lake, cache, Comparator or CI, and changed no mathematical
source, shared worktree, Git, publication, problem status or accepted count.
Root owns all actual compilation and later canonical/publication checks.

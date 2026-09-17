# RA-02 semantic API investigation

Bounded read-only source investigation by `/root/ie13_continuation`, at Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. These are mathematical implementation routes and inspected interfaces, not Lean proof bodies, an elaboration test, or an acceptance claim. The statement author received the findings directly. No original target or source was changed.

## Ordered smallest eigenvalue and genuine tail

Use `Matrix.IsHermitian.eigenvalues₀`, whose definition in `Analysis/Matrix/Spectrum.lean:58` is the decreasing eigenvalue list of the corresponding symmetric Euclidean linear map. `eigenvalues₀_antitone` is at line 61. The ordinary `eigenvalues` function at line 65 is a cardinality-equivalence reindexing and must not be assumed ordered by its matrix index. Preserve an explicit transport from `Fin n` to `Fin (Fintype.card (Fin n))` in the definition if needed.

A concise route to the last eigenvalue's Rayleigh inequality uses existing opaque theorems rather than expanding a chosen eigenbasis:

1. For the actual map `T = Matrix.toEuclideanLin A`, `LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional` (`Analysis/InnerProductSpace/Rayleigh.lean:345`) says the real infimum of `re ⟪T x,x⟫ / ‖x‖²`, over all nonzero x, is an eigenvalue. The original n≥1 supplies the required nontrivial Euclidean space.
2. `LinearMap.IsSymmetric.exists_eigenvalues_eq` (`Spectrum.lean:283`) places this eigenvalue in the decreasing list. `eigenvalues_antitone` (line 312) puts the last list entry below it.
3. `ciInf_le`, with a proved lower bound, puts that infimum below the quotient of the specified nonzero vector. For PSD A, `Matrix.PosSemidef.re_dotProduct_nonneg` (`Analysis/Matrix/PosDef.lean:45`) supplies lower bound zero. The real part of the inner product has the required orientation by `inner_re_symm` (`InnerProductSpace/Basic.lean:79`). Thus the PSD case needs no operator-norm bound. If a general Hermitian helper is desired, `ContinuousLinearMap.rayleighQuotient_le_norm` (`Rayleigh.lean:112`) gives a lower bound by minus the operator norm instead.
4. Pass from the map's ordered list to the matrix wrapper definition and from the Euclidean inner product to the actual conjugate dot product. The nonzero-vector denominator is strictly positive. The desired statement uses the genuine Rayleigh quotient of A and q, not an assumed eigenvalue list or a separately defined minimum.

For positive-definite A, `Matrix.PosDef.eigenvalues_pos` (`Analysis/Matrix/PosDef.lean:82`) gives strict positivity of every matrix eigenvalue. Transport through the same cardinality equivalence to obtain positivity of every ordered entry, especially the last. An alternative is to use `hasEigenvector_eigenvectorBasis` (`InnerProductSpace/Spectrum.lean:306`) and the strict quadratic form, but the existing positivity theorem avoids that extra expansion.

Define the original tail as the finite sum of ordered entries with zero-based index at least r. In dimension r+1, this filter contains exactly `Fin.last r`: the index inequalities force equality. `Finset.sum_eq_single` plus that arithmetic yields the actual tail equality, including r=1. At rank n the filter is empty and the tail is zero. Do not replace the tail by ε^r; only subsequently prove `0 < tail ≤ ε^r` using the explicitly nonzero test vector.

Keep `eigenvalues` and `eigenvectorBasis` opaque: their public sortedness, spectral membership and positivity APIs suffice. Their irreducible implementations use much larger spectral constructions which should not be unfolded during these proofs.

## Complex PSD Cholesky update and zero conventions

The exact generic PSD primitive is

`Matrix.PosSemidef.conjTranspose_mul_mul_same : PosSemidef R → PosSemidef (Bᴴ * R * B)`

in `LinearAlgebra/Matrix/PosDef.lean:313`. It applies to singular B. For a valid pivot j put a=R_jj, which is a strictly positive real scalar embedded in ℂ, and define the matrix B by

`B = I - e_j row_j(R)/a`.

An elementary matrix identity gives

`Bᴴ R B = R - col_j(R) row_j(R)/a`.

Indeed, conjugating B uses Hermitian symmetry of R and reality of a; in the expansion the two negative rank-one terms and the positive quadratic term combine because its middle scalar is R_jj=a. The right side is exactly the specified Cholesky residual, with the original division and multiplication order. Prove this equality as a small algebraic helper, then transfer PSD by the congruence lemma. No PSD square root, full Schur complement theory or dimension-dependent case enumeration is needed. `PosSemidef.fromBlocks₁₁` also exists at lines 563–578, but it adds avoidable finite-index reindexing and invertibility-instance work for this one-pivot step.

`Matrix.IsHermitian.apply` (`LinearAlgebra/Matrix/Hermitian.lean:62`) supplies the entrywise conjugate symmetry, including reality of the diagonal. `RCLike.conj_eq_iff_re` (`Analysis/RCLike/Basic.lean:375`) gives the exact equality between a real part embedded in ℂ and the self-conjugate scalar. This makes a real-diagonal sampling denominator provably equal to the complex pivot denominator.

For all PSD residuals, `PosSemidef.diag_nonneg` (`Linear PosDef:138`) and `trace_nonneg` (line 349) supply complex-order nonnegativity. `Complex.nonneg_iff` (`Analysis/Complex/Order.lean:63`) extracts both nonnegative real part and zero imaginary part. `PosSemidef.trace_eq_zero_iff` (`Analysis/Matrix/PosDef.lean:52`) gives complex trace zero iff the matrix is zero. Combining these gives real trace zero iff the matrix is zero, and strictly positive real trace for every nonzero PSD residual. The diagonal/trace weights are then nonnegative and their finite sum is exactly one.

A zero diagonal implies an entire zero row and column by a fixed 2×2 compression. For arbitrary i,j, `hR.submatrix ![i,j]` is PSD (`Linear PosDef:80`; no injectivity premise). Its determinant is nonnegative by `Analysis PosDef:48`. If R_jj=0, `Matrix.det_fin_two` (`Determinant/Basic.lean:807`) and Hermitian symmetry identify this determinant with `-Complex.normSq (R_i j)` embedded in ℂ. `Complex.normSq_nonneg` and `normSq_eq_zero` (`Data/Complex/Basic.lean:555,558`) force R_i j=0; symmetry gives the row as well. `Complex.mul_conj` at line 586 is the precise norm-square conversion. This is an analytic all-dimension lemma using one fixed small determinant formula, not a numerical finite-dimension surrogate.

At a positive pivot, direct division cancellation shows the selected row and column become zero. Any earlier zero row/column remains zero in the update. Therefore already selected labels have zero conditional probability and the explicit-family distinct-history formulas correspond to the actual process. If a totalized update is defined also at a zero diagonal, inverse-zero arithmetic returns R; its probability is zero, so it does not introduce a sampled invalid pivot.

At R=0, a dummy deterministic pivot label is permitted for n≥1 provided the update and all future residuals remain zero. State explicitly that this is the zero-absorption convention, not diagonal/trace division by zero. Generic path normalization and PSD preservation must cover this case and the full original range 1≤r≤n, even though the positive-definite counterexample only needs n=r+1 and remains nonzero during its first r steps.

These inspected interfaces suffice to support faithful complete statements. No further library search is presently needed. Proof implementation still waits for two independent statement approvals, actual Linux elaboration and immutable freeze. No Lean/Lake/cache, source or Git edits, workflow execution, publication or count change occurred in this investigation.

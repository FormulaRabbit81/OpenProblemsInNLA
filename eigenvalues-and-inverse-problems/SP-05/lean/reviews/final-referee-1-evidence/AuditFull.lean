import Solution
noncomputable section
open scoped BigOperators Matrix
open NLA.SP05
namespace Referee1

/-- The positive squared norm used to normalize the explicit skew-sector witness. -/
theorem exact_numerical_bound : (0 : ℝ) < 2 := NLA.SP05.numerical_bound
#assert_trust kernel exact_numerical_bound
#print axioms exact_numerical_bound

/-- Literal column stacking, Kronecker action, transposition and the Euclidean/Frobenius bridge. -/
theorem exact_column_vectorization {n : ℕ} (A B X : Mat n) :
    Matrix.kronecker A B *ᵥ columnVec X = columnVec (B * X * Aᵀ) ∧
    commutationMatrix n *ᵥ columnVec X = columnVec Xᵀ ∧
    dotProduct (columnVec X) (columnVec X) = frobeniusSq X := NLA.SP05.column_vectorization A B X
#assert_trust kernel exact_column_vectorization
#print axioms exact_column_vectorization

/-- Nonemptiness of the full skew sector is proved in every stated dimension. -/
theorem exact_skew_witness (n : ℕ) (hn : 2 ≤ n) :
    (skewExample n)ᵀ = -skewExample n ∧
    frobeniusSq (skewExample n) = 2 ∧ skewExample n ≠ 0 := NLA.SP05.skew_witness n hn
#assert_trust kernel exact_skew_witness
#print axioms exact_skew_witness

/-- A real nonzero PSD eigenmatrix attains the global minimum over all real vectors. -/
theorem exact_positive_minimizer (n : ℕ) (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ μ : ℝ, ∃ X : Mat n, 0 < μ ∧ X.PosSemidef ∧ X ≠ 0 ∧
      jordanMatrix A B *ᵥ columnVec X = μ • columnVec X ∧
      ∀ v : Vec n, v ≠ 0 → μ ≤ rayleigh (jordanMatrix A B) v := NLA.SP05.positive_minimizer n hn A B hA hB
#assert_trust kernel exact_positive_minimizer
#print axioms exact_positive_minimizer

/-- Both minima in the original formula are attained; no infimum of an empty set is substituted. -/
theorem exact_sector_minima (n : ℕ) (hn : 2 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ a b : ℝ, IsLeast (sectorValues A B 1) a ∧ IsLeast (sectorValues A B (-1)) b := NLA.SP05.sector_minima n hn A B hA hB
#assert_trust kernel exact_sector_minima
#print axioms exact_sector_minima

/-- The full original symmetric/skew Rayleigh-minimum inequality, for every positive definite pair. -/
theorem exact_canonical_result (n : ℕ) (hn : 2 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ a b : ℝ, IsLeast (sectorValues A B 1) a ∧
      IsLeast (sectorValues A B (-1)) b ∧ a ≤ b := NLA.SP05.canonical_result n hn A B hA hB
#assert_trust kernel exact_canonical_result
#print axioms exact_canonical_result

end Referee1

-- Check every project theorem, not only the public wrappers.
#assert_trust kernel NLA.SP05.kronecker_columnVec
#print axioms NLA.SP05.kronecker_columnVec
#assert_trust kernel NLA.SP05.commutation_mulVec
#print axioms NLA.SP05.commutation_mulVec
#assert_trust kernel NLA.SP05.commutation_columnVec
#print axioms NLA.SP05.commutation_columnVec
#assert_trust kernel NLA.SP05.columnVec_dot_self
#print axioms NLA.SP05.columnVec_dot_self
#assert_trust kernel NLA.SP05.columnVec_ne_zero
#print axioms NLA.SP05.columnVec_ne_zero
#assert_trust kernel NLA.SP05.dot_self_pos
#print axioms NLA.SP05.dot_self_pos
#assert_trust kernel NLA.SP05.skew_transpose
#print axioms NLA.SP05.skew_transpose
#assert_trust kernel NLA.SP05.skew_frobenius
#print axioms NLA.SP05.skew_frobenius
#assert_trust kernel NLA.SP05.skew_frobenius_pos
#print axioms NLA.SP05.skew_frobenius_pos
#assert_trust kernel NLA.SP05.skew_ne_zero
#print axioms NLA.SP05.skew_ne_zero
#assert_trust kernel NLA.SP05.skew_norm_positive_certificate
#print axioms NLA.SP05.skew_norm_positive_certificate
#assert_trust kernel NLA.SP05.complexify_apply
#print axioms NLA.SP05.complexify_apply
#assert_trust kernel NLA.SP05.complexifyHom_apply
#print axioms NLA.SP05.complexifyHom_apply
#assert_trust kernel NLA.SP05.complexify_injective
#print axioms NLA.SP05.complexify_injective
#assert_trust kernel NLA.SP05.complexify_zero
#print axioms NLA.SP05.complexify_zero
#assert_trust kernel NLA.SP05.complexify_eq_zero
#print axioms NLA.SP05.complexify_eq_zero
#assert_trust kernel NLA.SP05.complexify_add
#print axioms NLA.SP05.complexify_add
#assert_trust kernel NLA.SP05.complexify_sub
#print axioms NLA.SP05.complexify_sub
#assert_trust kernel NLA.SP05.complexify_smul
#print axioms NLA.SP05.complexify_smul
#assert_trust kernel NLA.SP05.complexify_star
#print axioms NLA.SP05.complexify_star
#assert_trust kernel NLA.SP05.complexify_conjTranspose
#print axioms NLA.SP05.complexify_conjTranspose
#assert_trust kernel NLA.SP05.complexify_transpose
#print axioms NLA.SP05.complexify_transpose
#assert_trust kernel NLA.SP05.complexify_one
#print axioms NLA.SP05.complexify_one
#assert_trust kernel NLA.SP05.complexify_mul
#print axioms NLA.SP05.complexify_mul
#assert_trust kernel NLA.SP05.complexify_posSemidef
#print axioms NLA.SP05.complexify_posSemidef
#assert_trust kernel NLA.SP05.complexify_posDef
#print axioms NLA.SP05.complexify_posDef
#assert_trust kernel NLA.SP05.complexify_inv
#print axioms NLA.SP05.complexify_inv
#assert_trust kernel NLA.SP05.complexify_sqrt
#print axioms NLA.SP05.complexify_sqrt
#assert_trust kernel NLA.SP05.complexify_abs
#print axioms NLA.SP05.complexify_abs
#assert_trust kernel NLA.SP05.complexify_abs_I_smul
#print axioms NLA.SP05.complexify_abs_I_smul
#assert_trust kernel NLA.SP05.complexify_kronecker
#print axioms NLA.SP05.complexify_kronecker
#assert_trust kernel NLA.SP05.complex_jordan_columnVec
#print axioms NLA.SP05.complex_jordan_columnVec
#assert_trust kernel NLA.SP05.actual_jordan_inverse_equation
#print axioms NLA.SP05.actual_jordan_inverse_equation
#assert_trust kernel NLA.SP05.actual_jordan_inverse_cone
#print axioms NLA.SP05.actual_jordan_inverse_cone
#assert_trust kernel NLA.SP05.jordan_posDef
#print axioms NLA.SP05.jordan_posDef
#assert_trust kernel NLA.SP05.jordan_commutation
#print axioms NLA.SP05.jordan_commutation
#assert_trust kernel NLA.SP05.jordan_inverse_commutation
#print axioms NLA.SP05.jordan_inverse_commutation
#assert_trust kernel NLA.SP05.real_eigenmatrix_sign
#print axioms NLA.SP05.real_eigenmatrix_sign
#assert_trust kernel NLA.SP05.jordan_inverse_top_sign
#print axioms NLA.SP05.jordan_inverse_top_sign
#assert_trust kernel NLA.SP05.inverse_eigen_to_eigen
#print axioms NLA.SP05.inverse_eigen_to_eigen
#assert_trust kernel NLA.SP05.rayleigh_lower_of_slack
#print axioms NLA.SP05.rayleigh_lower_of_slack
#assert_trust kernel NLA.SP05.global_positive_minimizer
#print axioms NLA.SP05.global_positive_minimizer
#assert_trust kernel NLA.SP05.vec_realMatrixAction
#print axioms NLA.SP05.vec_realMatrixAction
#assert_trust kernel NLA.SP05.vec_complexMatrixAction
#print axioms NLA.SP05.vec_complexMatrixAction
#assert_trust kernel NLA.SP05.complexMatrixAction_real
#print axioms NLA.SP05.complexMatrixAction_real
#assert_trust kernel NLA.SP05.complexPairing_trace
#print axioms NLA.SP05.complexPairing_trace
#assert_trust kernel NLA.SP05.complexPairing_real
#print axioms NLA.SP05.complexPairing_real
#assert_trust kernel NLA.SP05.complexPairing_I
#print axioms NLA.SP05.complexPairing_I
#assert_trust kernel NLA.SP05.trace_product_posSemidef_nonneg
#print axioms NLA.SP05.trace_product_posSemidef_nonneg
#assert_trust kernel NLA.SP05.complexPairing_posSemidef_nonneg
#print axioms NLA.SP05.complexPairing_posSemidef_nonneg
#assert_trust kernel NLA.SP05.hermitian_modulus_pairing_le
#print axioms NLA.SP05.hermitian_modulus_pairing_le
#assert_trust kernel NLA.SP05.real_abs_vec_norm_sq
#print axioms NLA.SP05.real_abs_vec_norm_sq
#assert_trust kernel NLA.SP05.modulus_quadratic_improves
#print axioms NLA.SP05.modulus_quadratic_improves
#assert_trust kernel NLA.SP05.numerical_bound
#print axioms NLA.SP05.numerical_bound
#assert_trust kernel NLA.SP05.column_vectorization
#print axioms NLA.SP05.column_vectorization
#assert_trust kernel NLA.SP05.skew_witness
#print axioms NLA.SP05.skew_witness
#assert_trust kernel NLA.SP05.positive_minimizer
#print axioms NLA.SP05.positive_minimizer
#assert_trust kernel NLA.SP05.sector_minima
#print axioms NLA.SP05.sector_minima
#assert_trust kernel NLA.SP05.canonical_result
#print axioms NLA.SP05.canonical_result
#assert_trust kernel NLA.SP05.dot_self_smul
#print axioms NLA.SP05.dot_self_smul
#assert_trust kernel NLA.SP05.rayleigh_smul
#print axioms NLA.SP05.rayleigh_smul
#assert_trust kernel NLA.SP05.normalize_sector
#print axioms NLA.SP05.normalize_sector
#assert_trust kernel NLA.SP05.unitSector_isCompact
#print axioms NLA.SP05.unitSector_isCompact
#assert_trust kernel NLA.SP05.unitSector_ne_zero
#print axioms NLA.SP05.unitSector_ne_zero
#assert_trust kernel NLA.SP05.sector_minimum_exists
#print axioms NLA.SP05.sector_minimum_exists
#assert_trust kernel NLA.SP05.symmetric_sector_nonempty
#print axioms NLA.SP05.symmetric_sector_nonempty
#assert_trust kernel NLA.SP05.skew_sector_nonempty
#print axioms NLA.SP05.skew_sector_nonempty
#assert_trust kernel NLA.SP05.both_sector_minima
#print axioms NLA.SP05.both_sector_minima
#assert_trust kernel NLA.SP05.commutation_dot
#print axioms NLA.SP05.commutation_dot
#assert_trust kernel NLA.SP05.commutation_kronecker
#print axioms NLA.SP05.commutation_kronecker
#assert_trust kernel NLA.SP05.sector_rayleigh_twice
#print axioms NLA.SP05.sector_rayleigh_twice
#assert_trust kernel NLA.SP05.rayleigh_of_eigenvector
#print axioms NLA.SP05.rayleigh_of_eigenvector
#assert_trust kernel NLA.SP05.sector_comparison_of_psd_minimizer
#print axioms NLA.SP05.sector_comparison_of_psd_minimizer
#assert_trust kernel NLA.SP05.real_spectral_max
#print axioms NLA.SP05.real_spectral_max
#assert_trust kernel NLA.SP05.psd_slack_eigenvector
#print axioms NLA.SP05.psd_slack_eigenvector
#assert_trust kernel NLA.SP05.inverse_slack_lower
#print axioms NLA.SP05.inverse_slack_lower
#assert_trust kernel NLA.SP05.sylvester_posSemidef
#print axioms NLA.SP05.sylvester_posSemidef
#assert_trust kernel NLA.SP05.complex_jordan_injective
#print axioms NLA.SP05.complex_jordan_injective
#assert_trust kernel NLA.SP05.complex_jordan_preimage_hermitian
#print axioms NLA.SP05.complex_jordan_preimage_hermitian
#assert_trust kernel NLA.SP05.complex_jordan_preimage_posSemidef
#print axioms NLA.SP05.complex_jordan_preimage_posSemidef
#assert_trust kernel NLA.SP05.complex_jordan_solution_posSemidef
#print axioms NLA.SP05.complex_jordan_solution_posSemidef

-- Actual smallest allowed positive dimension and nonempty original sectors.
namespace Referee1
open NLA.SP05
 theorem nonvacuous_positive_dimension :
    ∃ μ : ℝ, ∃ X : Mat 1, 0 < μ ∧ X.PosSemidef ∧ X ≠ 0 ∧
      jordanMatrix (1 : Mat 1) 1 *ᵥ columnVec X = μ • columnVec X ∧
      ∀ v : Vec 1, v ≠ 0 → μ ≤ rayleigh (jordanMatrix 1 1) v :=
  positive_minimizer 1 (by norm_num) 1 1 Matrix.PosDef.one Matrix.PosDef.one
 theorem nonvacuous_original_dimension :
    ∃ a b : ℝ, IsLeast (sectorValues (1 : Mat 2) 1 1) a ∧
      IsLeast (sectorValues (1 : Mat 2) 1 (-1)) b ∧ a ≤ b :=
  canonical_result 2 (by norm_num) 1 1 Matrix.PosDef.one Matrix.PosDef.one
 #assert_trust kernel nonvacuous_positive_dimension
 #print axioms nonvacuous_positive_dimension
 #assert_trust kernel nonvacuous_original_dimension
 #print axioms nonvacuous_original_dimension
end Referee1

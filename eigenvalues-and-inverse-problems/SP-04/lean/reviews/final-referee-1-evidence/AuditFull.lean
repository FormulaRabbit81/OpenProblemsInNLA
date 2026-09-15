import Solution
noncomputable section
open scoped BigOperators Matrix
open NLA.SP04
namespace Referee1
theorem exact_numerical_bounds :
    (99 / 100 : ℝ) ^ 2 < 49 / 16 - 52 / 25 ∧
    (275 / 198 : ℝ) < 2 ∧
    (13 / 25 : ℝ) * (44 / 25) * (51 / 50) < 1 ∧
    (201 / 400 : ℝ) < 13 / 25 := NLA.SP04.numerical_bounds 
#assert_trust kernel exact_numerical_bounds
#print axioms exact_numerical_bounds
theorem exact_diagonal_stationary_iff (s : Fin 3 → ℝ) (hs : Admissible s)
    (X : Mat 3) (c : ℝ) :
    Stationary (Matrix.diagonal s) X c ↔
      ∃ x : Fin 3 → ℝ, X = Matrix.diagonal x ∧
        (∀ i, (x i) ^ 2 - s i * x i + c = 0) ∧ |∏ i, x i| = 1 := NLA.SP04.diagonal_stationary_iff s hs X c
#assert_trust kernel exact_diagonal_stationary_iff
#print axioms exact_diagonal_stationary_iff
theorem exact_diagonal_counterexample (s : Fin 3 → ℝ) (hs : Admissible s) :
    ∃ t : ℝ, 0 < t ∧ t < 13 / 25 ∧
      UniqueLeastStationary (Matrix.diagonal s) (selectedMatrix s t) (-t) ∧
      Feasible (improvedMatrix s t) ∧
      frobeniusNorm (Matrix.diagonal s - improvedMatrix s t) <
        frobeniusNorm (Matrix.diagonal s - selectedMatrix s t) := NLA.SP04.diagonal_counterexample s hs
#assert_trust kernel exact_diagonal_counterexample
#print axioms exact_diagonal_counterexample
theorem exact_diagonal_finite (s : Fin 3 → ℝ) (hs : Admissible s) :
    (stationaryPairs (Matrix.diagonal s)).Finite := NLA.SP04.diagonal_finite s hs
#assert_trust kernel exact_diagonal_finite
#print axioms exact_diagonal_finite
theorem exact_orthogonal_transport {n : ℕ} (P Q U X : Mat n) (c : ℝ)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    (Feasible (P * X * Qᵀ) ↔ Feasible X) ∧
    frobeniusNorm (P * (U - X) * Qᵀ) = frobeniusNorm (U - X) ∧
    (Stationary (P * U * Qᵀ) (P * X * Qᵀ) c ↔ Stationary U X c) := NLA.SP04.orthogonal_transport P Q U X c hP hQ
#assert_trust kernel exact_orthogonal_transport
#print axioms exact_orthogonal_transport
theorem exact_spectral_family :
    IsOpen counterexampleFamily ∧ sampleMatrix ∈ counterexampleFamily ∧
      ∀ U ∈ counterexampleFamily, ∃ s : Fin 3 → ℝ, Admissible s ∧ HasSVD U s := NLA.SP04.spectral_family 
#assert_trust kernel exact_spectral_family
#print axioms exact_spectral_family
theorem exact_regular_svd (U : Mat 3) (s : Fin 3 → ℝ)
    (hs : Admissible s) (hsvd : HasSVD U s) : RegularData U := NLA.SP04.regular_svd U s hs hsvd
#assert_trust kernel exact_regular_svd
#print axioms exact_regular_svd
theorem exact_open_family_counterexamples : ∀ U ∈ counterexampleFamily, SelectionFails U := NLA.SP04.open_family_counterexamples 
#assert_trust kernel exact_open_family_counterexamples
#print axioms exact_open_family_counterexamples
theorem exact_algebraic_avoidance (S : Set (Mat 3)) (hS : IsOpen S) (hne : S.Nonempty)
    (p : MvPolynomial (Fin 3 × Fin 3) ℝ) (hp : p ≠ 0) :
    ∃ U ∈ S, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 := NLA.SP04.algebraic_avoidance S hS hne p hp
#assert_trust kernel exact_algebraic_avoidance
#print axioms exact_algebraic_avoidance
theorem exact_generic_counterexamples (p : MvPolynomial (Fin 3 × Fin 3) ℝ) (hp : p ≠ 0) :
    ∃ U : Mat 3, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 ∧ SelectionFails U := NLA.SP04.generic_counterexamples p hp
#assert_trust kernel exact_generic_counterexamples
#print axioms exact_generic_counterexamples
theorem exact_canonical_counterexample : ¬ AllGenericSelectionRules := NLA.SP04.canonical_counterexample 
#assert_trust kernel exact_canonical_counterexample
#print axioms exact_canonical_counterexample
#check NLA.SP04.scalar_numerical_bounds
#assert_trust kernel NLA.SP04.scalar_numerical_bounds
#print axioms NLA.SP04.scalar_numerical_bounds
#check NLA.SP04.selected_parameter_exists
#assert_trust kernel NLA.SP04.selected_parameter_exists
#print axioms NLA.SP04.selected_parameter_exists
#check NLA.SP04.nonnegative_scalar_impossible
#assert_trust kernel NLA.SP04.nonnegative_scalar_impossible
#print axioms NLA.SP04.nonnegative_scalar_impossible
#check NLA.SP04.negative_scalar_comparison
#assert_trust kernel NLA.SP04.negative_scalar_comparison
#print axioms NLA.SP04.negative_scalar_comparison
#check NLA.SP04.scalar_least_unique
#assert_trust kernel NLA.SP04.scalar_least_unique
#print axioms NLA.SP04.scalar_least_unique
#check NLA.SP04.scalar_distance_improves
#assert_trust kernel NLA.SP04.scalar_distance_improves
#print axioms NLA.SP04.scalar_distance_improves
#check NLA.SP04.stationary_gram_commutes
#assert_trust kernel NLA.SP04.stationary_gram_commutes
#print axioms NLA.SP04.stationary_gram_commutes
#check NLA.SP04.stationary_diagonal_matrix
#assert_trust kernel NLA.SP04.stationary_diagonal_matrix
#print axioms NLA.SP04.stationary_diagonal_matrix
#check NLA.SP04.stationaryEliminant_at_zero
#assert_trust kernel NLA.SP04.stationaryEliminant_at_zero
#print axioms NLA.SP04.stationaryEliminant_at_zero
#check NLA.SP04.stationaryEliminant_ne_zero
#assert_trust kernel NLA.SP04.stationaryEliminant_ne_zero
#print axioms NLA.SP04.stationaryEliminant_ne_zero
#check NLA.SP04.scalar_stationary_eliminant
#assert_trust kernel NLA.SP04.scalar_stationary_eliminant
#print axioms NLA.SP04.scalar_stationary_eliminant
#check NLA.SP04.diagonal_stationary_finite
#assert_trust kernel NLA.SP04.diagonal_stationary_finite
#print axioms NLA.SP04.diagonal_stationary_finite
#check NLA.SP04.frobeniusNorm_orthogonal
#assert_trust kernel NLA.SP04.frobeniusNorm_orthogonal
#print axioms NLA.SP04.frobeniusNorm_orthogonal
#check NLA.SP04.stationaryPairs_orthogonal_eq
#assert_trust kernel NLA.SP04.stationaryPairs_orthogonal_eq
#print axioms NLA.SP04.stationaryPairs_orthogonal_eq
#check NLA.SP04.uniqueLeastStationary_orthogonal_iff
#assert_trust kernel NLA.SP04.uniqueLeastStationary_orthogonal_iff
#print axioms NLA.SP04.uniqueLeastStationary_orthogonal_iff
#check NLA.SP04.gram_root_in_interval
#assert_trust kernel NLA.SP04.gram_root_in_interval
#print axioms NLA.SP04.gram_root_in_interval
#check NLA.SP04.reordered_gram_basis
#assert_trust kernel NLA.SP04.reordered_gram_basis
#print axioms NLA.SP04.reordered_gram_basis
#check NLA.SP04.family_has_admissible_svd
#assert_trust kernel NLA.SP04.family_has_admissible_svd
#print axioms NLA.SP04.family_has_admissible_svd
#check NLA.SP04.admissible_svd_regular
#assert_trust kernel NLA.SP04.admissible_svd_regular
#print axioms NLA.SP04.admissible_svd_regular
#check NLA.SP04.polynomial_avoids_open
#assert_trust kernel NLA.SP04.polynomial_avoids_open
#print axioms NLA.SP04.polynomial_avoids_open
#check NLA.SP04.selectionFails_of_admissible_svd
#assert_trust kernel NLA.SP04.selectionFails_of_admissible_svd
#print axioms NLA.SP04.selectionFails_of_admissible_svd
theorem actual_nonempty_failure : ∃ U : Mat 3, SelectionFails U := by
  obtain ⟨U, _, h⟩ := NLA.SP04.generic_counterexamples (1 : MvPolynomial (Fin 3 × Fin 3) ℝ) (by norm_num)
  exact ⟨U,h⟩
#assert_trust kernel actual_nonempty_failure
#print axioms actual_nonempty_failure
end Referee1

import Solution

noncomputable section

namespace NLA.IE17

set_option leancert.trust "kernel"

theorem referee1_spectralNorm_semantics {m n : ℕ} (E : Mat m n) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ spectralNorm E ∧
      (spectralNorm E ≤ c ↔ ∀ y : Vec n, ‖E.toEuclideanLin y‖ ≤ c * ‖y‖) := NLA.IE17.spectralNorm_semantics E c hc

#assert_trust kernel referee1_spectralNorm_semantics

#print axioms referee1_spectralNorm_semantics

theorem referee1_witness_full_column_rank : Function.Injective witnessA.toEuclideanLin := NLA.IE17.witness_full_column_rank

#assert_trust kernel referee1_witness_full_column_rank

#print axioms referee1_witness_full_column_rank

theorem referee1_exact_lsmr_run :
    IsTerminatingLSMRRun witnessA witnessB witnessRun ∧
    witnessX₁ ≠ 0 ∧ witnessX₂ ≠ 0 ∧ witnessX₃ ≠ 0 := NLA.IE17.exact_lsmr_run

#assert_trust kernel referee1_exact_lsmr_run

#print axioms referee1_exact_lsmr_run

theorem referee1_optimal_errors :
    ∃ μ₁ μ₂ : ℝ,
      IsOptimalError witnessA witnessB witnessX₁ μ₁ ∧
      IsOptimalError witnessA witnessB witnessX₂ μ₂ ∧
      0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
      μ₁ ^ 2 ≤ (1979 : ℝ) / 2000 ∧ (99 : ℝ) / 100 < μ₂ ^ 2 := NLA.IE17.optimal_errors

#assert_trust kernel referee1_optimal_errors

#print axioms referee1_optimal_errors

theorem referee1_approximation_values :
    ∃ q₁ q₂ : ℝ,
      IsApproximation witnessA witnessB witnessX₁ q₁ ∧
      IsApproximation witnessA witnessB witnessX₂ q₂ ∧
      (∀ q, IsApproximation witnessA witnessB witnessX₁ q → q = q₁) ∧
      (∀ q, IsApproximation witnessA witnessB witnessX₂ q → q = q₂) ∧
      0 ≤ q₁ ∧ 0 ≤ q₂ ∧
      q₁ ^ 2 = (69694107852573439503892031925 : ℝ) / 69323394392991282508138323472 ∧
      q₂ ^ 2 = (5430772101137459612205263871781350 : ℝ) / 5387955615790281743396033884265233 := NLA.IE17.approximation_values

#assert_trust kernel referee1_approximation_values

#print axioms referee1_approximation_values

theorem referee1_terminal_errors_zero :
    IsOptimalError witnessA witnessB witnessX₃ 0 ∧
    IsApproximation witnessA witnessB witnessX₃ 0 := NLA.IE17.terminal_errors_zero

#assert_trust kernel referee1_terminal_errors_zero

#print axioms referee1_terminal_errors_zero

theorem referee1_both_errors_increase :
    ∃ μ₁ μ₂ q₁ q₂ : ℝ,
      IsOptimalError witnessA witnessB witnessX₁ μ₁ ∧
      IsOptimalError witnessA witnessB witnessX₂ μ₂ ∧
      IsApproximation witnessA witnessB witnessX₁ q₁ ∧
      IsApproximation witnessA witnessB witnessX₂ q₂ ∧
      μ₁ < μ₂ ∧ q₁ < q₂ ∧
      μ₁ ^ 2 ≤ (1979 : ℝ) / 2000 ∧ (1979 : ℝ) / 2000 < (99 : ℝ) / 100 ∧
      (99 : ℝ) / 100 < μ₂ ^ 2 ∧
      q₁ ^ 2 < (503 : ℝ) / 500 ∧ (503 : ℝ) / 500 < (1007 : ℝ) / 1000 ∧
      (1007 : ℝ) / 1000 < q₂ ^ 2 := NLA.IE17.both_errors_increase

#assert_trust kernel referee1_both_errors_increase

#print axioms referee1_both_errors_increase

theorem referee1_canonical_counterexamples :
    ¬ OptimalErrorsNonincreasing ∧ ¬ ApproximationErrorsNonincreasing := NLA.IE17.canonical_counterexamples

#assert_trust kernel referee1_canonical_counterexamples

#print axioms referee1_canonical_counterexamples

#assert_trust kernel certificate_cutoffs

#print axioms certificate_cutoffs

#assert_trust kernel exists_optimal_error

#print axioms exists_optimal_error

#assert_trust kernel feasible_direction_bounds

#print axioms feasible_direction_bounds

#assert_trust kernel witnessE_feasible

#print axioms witnessE_feasible

#assert_trust kernel witnessE_norm_sq_bound

#print axioms witnessE_norm_sq_bound

#assert_trust kernel lower_quadratic_certificate

#print axioms lower_quadratic_certificate

#assert_trust kernel zero_new_residual_certificate

#print axioms zero_new_residual_certificate

#assert_trust kernel optimal_error_bounds

#print axioms optimal_error_bounds

#assert_trust kernel penrose_projection_unique

#print axioms penrose_projection_unique

#assert_trust kernel penroseAt_correct

#print axioms penroseAt_correct

#assert_trust kernel projection_norm_sq

#print axioms projection_norm_sq

#assert_trust kernel actualQ_one_sq

#print axioms actualQ_one_sq

#assert_trust kernel actualQ_two_sq

#print axioms actualQ_two_sq

#assert_trust kernel approximation_error_values

#print axioms approximation_error_values

#assert_trust kernel witness_run_exact

#print axioms witness_run_exact

end NLA.IE17

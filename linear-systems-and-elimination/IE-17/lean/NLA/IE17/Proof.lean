/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.Optimal
import NLA.IE17.Approximation
import NLA.IE17.LSMR
import LeanCert.Tactic

set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE17

/-- This is the Euclidean induced norm on every real matrix and test vector. -/
theorem spectralNorm_semantics {m n : ℕ} (E : Mat m n) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ spectralNorm E ∧
      (spectralNorm E ≤ c ↔ ∀ y : Vec n, ‖E.toEuclideanLin y‖ ≤ c * ‖y‖) := by
  exact ⟨spectralNorm_nonneg E, spectralNorm_le_iff E hc⟩

/-- The exhibited integer matrix has full column rank. -/
theorem witness_full_column_rank : Function.Injective witnessA.toEuclideanLin := by
  exact witnessA_injective

/-- Actual exact LSMR, zero start, minimum-length convention, and first termination at step 3. -/
theorem exact_lsmr_run :
    IsTerminatingLSMRRun witnessA witnessB witnessRun ∧
    witnessX₁ ≠ 0 ∧ witnessX₂ ≠ 0 ∧ witnessX₃ ≠ 0 := by
  exact witness_run_exact

/-- The optimal values are attained over ALL real spectral-norm perturbations with b fixed. -/
theorem optimal_errors :
    ∃ μ₁ μ₂ : ℝ,
      IsOptimalError witnessA witnessB witnessX₁ μ₁ ∧
      IsOptimalError witnessA witnessB witnessX₂ μ₂ ∧
      0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
      μ₁ ^ 2 ≤ (1979 : ℝ) / 2000 ∧ (99 : ℝ) / 100 < μ₂ ^ 2 := by
  exact optimal_error_bounds

/-- Genuine Moore–Penrose values, exact squares and uniqueness for both nonzero iterates. -/
theorem approximation_values :
    ∃ q₁ q₂ : ℝ,
      IsApproximation witnessA witnessB witnessX₁ q₁ ∧
      IsApproximation witnessA witnessB witnessX₂ q₂ ∧
      (∀ q, IsApproximation witnessA witnessB witnessX₁ q → q = q₁) ∧
      (∀ q, IsApproximation witnessA witnessB witnessX₂ q → q = q₂) ∧
      0 ≤ q₁ ∧ 0 ≤ q₂ ∧
      q₁ ^ 2 = (69694107852573439503892031925 : ℝ) / 69323394392991282508138323472 ∧
      q₂ ^ 2 = (5430772101137459612205263871781350 : ℝ) / 5387955615790281743396033884265233 := by
  exact approximation_error_values

/-- Both canonical errors vanish at the exact least-squares terminal iterate. -/
theorem terminal_errors_zero :
    IsOptimalError witnessA witnessB witnessX₃ 0 ∧
    IsApproximation witnessA witnessB witnessX₃ 0 := by
  refine ⟨optimal_zero_of_normalResidual_zero witness_normalResidual_three, ?_⟩
  simp [IsApproximation, witnessX₃_ne_zero, witness_normalResidual_three]

/-- Both errors strictly increase at the SAME successive nonzero LSMR iterates. -/
theorem both_errors_increase :
    ∃ μ₁ μ₂ q₁ q₂ : ℝ,
      IsOptimalError witnessA witnessB witnessX₁ μ₁ ∧
      IsOptimalError witnessA witnessB witnessX₂ μ₂ ∧
      IsApproximation witnessA witnessB witnessX₁ q₁ ∧
      IsApproximation witnessA witnessB witnessX₂ q₂ ∧
      μ₁ < μ₂ ∧ q₁ < q₂ ∧
      μ₁ ^ 2 ≤ (1979 : ℝ) / 2000 ∧ (1979 : ℝ) / 2000 < (99 : ℝ) / 100 ∧
      (99 : ℝ) / 100 < μ₂ ^ 2 ∧
      q₁ ^ 2 < (503 : ℝ) / 500 ∧ (503 : ℝ) / 500 < (1007 : ℝ) / 1000 ∧
      (1007 : ℝ) / 1000 < q₂ ^ 2 := by
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hnμ₁, hnμ₂, hupper, hlower⟩ := optimal_errors
  obtain ⟨q₁, q₂, hq₁, hq₂, _, _, hnq₁, hnq₂, hsq₁, hsq₂⟩ := approximation_values
  have hcut : (1979 : ℝ) / 2000 < (99 : ℝ) / 100 := certificate_cutoffs.2.1
  have hμ : μ₁ < μ₂ :=
    (sq_lt_sq₀ hnμ₁ hnμ₂).mp (hupper.trans_lt (hcut.trans hlower))
  have hfirst : q₁ ^ 2 < (503 : ℝ) / 500 := by
    rw [hsq₁]
    norm_num
  have hmiddle : (503 : ℝ) / 500 < (1007 : ℝ) / 1000 := by norm_num
  have hsecond : (1007 : ℝ) / 1000 < q₂ ^ 2 := by
    rw [hsq₂]
    norm_num
  have hq : q₁ < q₂ :=
    (sq_lt_sq₀ hnq₁ hnq₂).mp (hfirst.trans (hmiddle.trans hsecond))
  exact ⟨μ₁, μ₂, q₁, q₂, hμ₁, hμ₂, hq₁, hq₂, hμ, hq,
    hupper, hcut, hlower, hfirst, hmiddle, hsecond⟩

/-- Each original monotonicity claim fails, against the independently reviewed definitions. -/
theorem canonical_counterexamples :
    ¬ OptimalErrorsNonincreasing ∧ ¬ ApproximationErrorsNonincreasing := by
  obtain ⟨μ₁, μ₂, q₁, q₂, hμ₁, hμ₂, hq₁, hq₂, hμ, hq, _⟩ := both_errors_increase
  constructor
  · intro hmonotone
    have hle : μ₂ ≤ μ₁ := hmonotone 4 3 3 witnessA witnessB witnessRun exact_lsmr_run.1
      (1 : Fin 4) (2 : Fin 4) (by norm_num) witnessX₁_ne_zero witnessX₂_ne_zero
      μ₁ μ₂ hμ₁ hμ₂
    exact (not_le_of_gt hμ) hle
  · intro hmonotone
    have hle : q₂ ≤ q₁ := hmonotone 4 3 3 witnessA witnessB witnessRun exact_lsmr_run.1
      (1 : Fin 4) (2 : Fin 4) (by norm_num) witnessX₁_ne_zero witnessX₂_ne_zero
      q₁ q₂ hq₁ hq₂
    exact (not_le_of_gt hq) hle

#assert_trust kernel spectralNorm_semantics
#assert_trust kernel witness_full_column_rank
#assert_trust kernel exact_lsmr_run
#assert_trust kernel optimal_errors
#assert_trust kernel approximation_values
#assert_trust kernel terminal_errors_zero
#assert_trust kernel both_errors_increase
#assert_trust kernel canonical_counterexamples

#print axioms spectralNorm_semantics
#print axioms witness_full_column_rank
#print axioms exact_lsmr_run
#print axioms optimal_errors
#print axioms approximation_values
#print axioms terminal_errors_zero
#print axioms both_errors_increase
#print axioms canonical_counterexamples

end NLA.IE17

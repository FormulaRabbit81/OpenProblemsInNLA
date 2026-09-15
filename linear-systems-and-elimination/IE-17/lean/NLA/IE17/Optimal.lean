/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.BackwardError
import NLA.IE17.Certificates

noncomputable section
open scoped InnerProductSpace
namespace NLA.IE17

lemma witnessE_spectral_sq_bound : spectralNorm witnessE ^ 2 ≤ (1979 : ℝ) / 2000 :=
  spectralNorm_sq_le_of_forall witnessE certificate_cutoffs.1.le witnessE_norm_sq_bound

/-- The bound quantifies over all real perturbations satisfying the original normal equations. -/
lemma every_feasible_second_lower (E : Mat 4 3)
    (hE : Feasible witnessA witnessB witnessX₂ E) :
    (9901 : ℝ) / 10000 ≤ spectralNorm E ^ 2 := by
  have hx : 0 < ‖witnessX₂‖ ^ 2 := by rw [witnessX₂_norm_sq]; norm_num
  by_cases hq : residual (witnessA + E) witnessB witnessX₂ = 0
  · have h := (zero_new_residual_certificate).trans (feasible_zero_residual_bound hq)
    exact (mul_le_mul_iff_left₀ hx).mp h
  · obtain ⟨u, hu, hC, hD⟩ := feasible_direction_bounds hE hq
    have hcert := lower_quadratic_certificate u
    rw [← inner_eq_sum, ← inner_eq_sum,
      real_inner_comm u (residual witnessA witnessB witnessX₂),
      real_inner_comm u (witnessA.toEuclideanLin witnessX₂)] at hcert
    simp only [hu, one_pow, mul_one] at hcert
    have hratio := (div_le_iff₀ hx).mpr hD
    have hcombined :
        (5 : ℝ) / 6 * ‖witnessA.transpose.toEuclideanLin u‖ ^ 2 +
        (1 : ℝ) / 6 *
          ((‖residual witnessA witnessB witnessX₂‖ ^ 2 -
            ⟪u, residual witnessA witnessB witnessX₂⟫_ℝ ^ 2 +
            ⟪u, witnessA.toEuclideanLin witnessX₂⟫_ℝ ^ 2) / ‖witnessX₂‖ ^ 2)
        ≤ spectralNorm E ^ 2 := by nlinarith
    exact hcert.trans (by simpa only [mul_div_assoc] using hcombined)

lemma optimal_error_bounds :
    ∃ μ₁ μ₂ : ℝ,
      IsOptimalError witnessA witnessB witnessX₁ μ₁ ∧
      IsOptimalError witnessA witnessB witnessX₂ μ₂ ∧
      0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
      μ₁ ^ 2 ≤ (1979 : ℝ) / 2000 ∧ (99 : ℝ) / 100 < μ₂ ^ 2 := by
  obtain ⟨μ₁, h₁⟩ := exists_optimal_error witnessA witnessB witnessX₁
  obtain ⟨μ₂, h₂⟩ := exists_optimal_error witnessA witnessB witnessX₂
  have hnonneg₁ := error_nonneg h₁
  have hnonneg₂ := error_nonneg h₂
  have hupper : μ₁ ≤ spectralNorm witnessE := h₁.2 ⟨witnessE, witnessE_feasible, rfl⟩
  have hupperSq : μ₁ ^ 2 ≤ spectralNorm witnessE ^ 2 :=
    pow_le_pow_left₀ hnonneg₁ hupper 2
  have hlower : (9901 : ℝ) / 10000 ≤ μ₂ ^ 2 := by
    obtain ⟨E, hE, rfl⟩ := h₂.1
    exact every_feasible_second_lower E hE
  exact ⟨μ₁, μ₂, h₁, h₂, hnonneg₁, hnonneg₂,
    hupperSq.trans witnessE_spectral_sq_bound, certificate_cutoffs.2.2.trans_le hlower⟩

#assert_trust kernel witnessE_spectral_sq_bound
#assert_trust kernel every_feasible_second_lower
#assert_trust kernel optimal_error_bounds
#print axioms optimal_error_bounds

end NLA.IE17

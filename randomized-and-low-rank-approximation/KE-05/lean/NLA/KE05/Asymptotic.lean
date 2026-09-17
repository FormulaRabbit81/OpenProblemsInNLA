import NLA.KE05.MatrixLimit
import NLA.KE05.ExtremumBounds
import NLA.KE05.TotalMeasurability

/- The source's coupled almost-sure limit and marginal-probability conclusion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace NLA.KE05

 theorem literal_lower_bound_proved (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ)/4)
    (w : Sample 2 3) (hw : Valid (witnessData e) w) :
    Real.rpow 8 (-(1 : ℝ)/4) *
      (spectralNorm ((recurrence (witnessData e) w 0).hat 1) / (2*e)) ≤
        totalConstant (witnessData e) w := by
  apply literal_lower_bound_of_det e he w hw
  · rw [first_lastS_determinant e w hw]
    have h1 : 0 < 2-e := by linarith [he.2]
    have h2 : 0 < 2-2*e := by linarith [he.2]
    positivity
  · rw [first_lastS_determinant e w hw]
    have h1 : 0 ≤ 2-e := by linarith [he.2]
    have h2 : 0 ≤ 2-2*e := by linarith [he.2]
    nlinarith [mul_nonneg he.1.le h1]

 theorem almost_sure_divergence_proved :
    ∀ᵐ w ∂gaussianLaw 2 3,
      Tendsto (fun m : ℕ => totalConstant (witnessData (epsilon m)) w) atTop atTop := by
  filter_upwards [probability_one_nonzero_limit_proved] with w hw
  have hn := continuous_spectralNorm.tendsto (limitMatrix w) |>.comp hw.2.2.2.1
  have hm : Tendsto (fun m : ℕ => ((m : ℝ)+6)/2) atTop atTop :=
    (tendsto_atTop_mono (fun m : ℕ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 6))
      tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hq := hn.pos_mul_atTop hw.2.2.2.2 hm
  have hc : 0 < Real.rpow 8 (-(1 : ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
  have heps (m : ℕ) : (2*epsilon m)⁻¹ = ((m : ℝ)+6)/2 := by
    simp [epsilon, div_eq_mul_inv, mul_inv_rev]
  have hq' : Tendsto (fun m : ℕ =>
      spectralNorm ((recurrence (witnessData (epsilon m)) w 0).hat 1)/(2*epsilon m))
      atTop atTop := by
    simpa only [div_eq_mul_inv, heps, Function.comp_def] using hq
  exact tendsto_atTop_mono (fun m => literal_lower_bound_proved (epsilon m)
    (epsilon_range m) w (hw.2.2.1 m)) (hq'.const_mul_atTop hc)

 theorem marginal_probability_limit_proved (C : ℝ) :
    Tendsto (fun m : ℕ => boundedProbability (witnessData (epsilon m)) C)
      atTop (nhds 0) :=
  probability_limit_of_divergence
    (fun m => measurable_totalConstant _ (witness_admissible _ (epsilon_range m)))
    almost_sure_divergence_proved C

 theorem no_finite_uniform_constant_proved :
    ∀ C : ℝ, ∃ L : Data 2 3,
      Admissible L ∧ boundedProbability L C < (1 : ℝ)/2 :=
  no_finite_constant_of_probability_limit marginal_probability_limit_proved

 theorem not_uniform_probability_conjecture_proved : ¬ UniformProbabilityConjecture :=
  negation_of_no_finite_constant no_finite_uniform_constant_proved

end NLA.KE05

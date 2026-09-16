import NLA.KE05.Endpoints

/- The marginal-probability step in George Stepaniants's proof. Mathlib's
indicator-convergence theorem supplies dominated convergence for finite measures. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace NLA.KE05

instance gaussianLaw_probability (b d : ℕ) : IsProbabilityMeasure (gaussianLaw b d) := by
  unfold gaussianLaw
  infer_instance

lemma probability_le_tendsto_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : ℕ → α → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hd : ∀ᵐ a ∂μ, Tendsto (fun n => f n a) atTop atTop) (C : ℝ) :
    Tendsto (fun n => (μ {a | f n a ≤ C}).toReal) atTop (nhds 0) := by
  have hlim : ∀ᵐ a ∂μ, ∀ᶠ n in atTop, a ∈ {a | f n a ≤ C} ↔ a ∈ (∅ : Set α) := by
    filter_upwards [hd] with a ha
    filter_upwards [ha.eventually_gt_atTop C] with n hn
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt hn
  have hm := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    atTop MeasurableSet.empty (fun n => measurableSet_le (hf n) measurable_const) hlim
  have hz : Tendsto (fun n => μ {a | f n a ≤ C}) atTop (nhds 0) := by simpa using hm
  simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hz

lemma epsilon_range (m : ℕ) : 0 < epsilon m ∧ epsilon m < (1 : ℝ) / 4 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · exact one_div_pos.mpr (by positivity)
  · unfold epsilon
    apply (div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)).mpr
    linarith

lemma probability_limit_of_divergence
    (hm : ∀ m, Measurable (totalConstant (witnessData (epsilon m))))
    (hd : ∀ᵐ w ∂gaussianLaw 2 3,
      Tendsto (fun m => totalConstant (witnessData (epsilon m)) w) atTop atTop)
    (C : ℝ) :
    Tendsto (fun m => boundedProbability (witnessData (epsilon m)) C) atTop (nhds 0) :=
  probability_le_tendsto_zero (gaussianLaw 2 3) _ hm hd C

lemma no_finite_constant_of_probability_limit
    (hl : ∀ C : ℝ, Tendsto (fun m => boundedProbability (witnessData (epsilon m)) C)
      atTop (nhds 0)) :
    ∀ C : ℝ, ∃ L : Data 2 3, Admissible L ∧ boundedProbability L C < (1 : ℝ) / 2 := by
  intro C
  have hh : ∀ᶠ m in atTop, boundedProbability (witnessData (epsilon m)) C < (1 : ℝ) / 2 :=
    (hl C).eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨m, hm⟩ := hh.exists
  exact ⟨witnessData (epsilon m), witness_admissible _ (epsilon_range m), hm⟩

lemma negation_of_no_finite_constant
    (hn : ∀ C : ℝ, ∃ L : Data 2 3,
      Admissible L ∧ boundedProbability L C < (1 : ℝ) / 2) :
    ¬ UniformProbabilityConjecture := by
  intro h
  obtain ⟨C,hC⟩ := h 2 3 (by decide) (by decide) (1/2) (by norm_num) (by norm_num)
  obtain ⟨L,hL,hh⟩ := hn C
  have hb := hC L hL
  linarith

end NLA.KE05

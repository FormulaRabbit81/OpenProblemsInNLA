import NLA.RowDeletion.Trimming
import NLA.RowDeletion.ThresholdGrid
import Mathlib.Probability.Moments.SubGaussian

/-! # Bounded concentration reused from Mathlib

The only new probability step is the two-sided union bound and normalization.
Hoeffding's lemma and independence of sums are imported, not reproved.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace NLA.RowDeletion

lemma measure_abs_gt_le_of_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε < |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hsub : {ω | ε < |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω hω
    change ε < |X ω| at hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have h := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  have hp := hX.measure_ge_le hε
  have hn := hX.neg.measure_ge_le hε
  change μ.real {ω | ε ≤ -X ω} ≤ _ at hn
  linarith

theorem bounded_average_concentration
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) (X : Fin m → Ω → ℝ)
    (hindep : iIndepFun X μ) (hXm : ∀ i, AEMeasurable (X i) μ)
    {L : ℝ} (hL : 0 < L) (hX : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 L)
    {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | η < |(∑ i, (X i ω - ∫ x, X i x ∂μ)) / m|} ≤
      2 * Real.exp (-2 * m * η ^ 2 / L ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hind : iIndepFun (fun i ω ↦ X i ω - ∫ x, X i x ∂μ) μ :=
    hindep.comp (fun i x ↦ x - ∫ ω, X i ω ∂μ) (fun _ ↦ by fun_prop)
  have hsub (i : Fin m) := hasSubgaussianMGF_of_mem_Icc (hXm i) (hX i)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind
    (s := Finset.univ) (fun i _ ↦ hsub i)
  have htail := measure_abs_gt_le_of_subgaussian hsum (mul_nonneg hm'.le hη)
  have hevent : {ω | η < |(∑ i, (X i ω - ∫ x, X i x ∂μ)) / m|} =
      {ω | (m : ℝ) * η < |∑ i, (X i ω - ∫ x, X i x ∂μ)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hm', lt_div_iff₀ hm']
    rw [mul_comm]
  rw [hevent]
  convert htail using 1
  simp only [sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hL]
  congr 2
  field_simp

/-- Every truncated-square statistic is bounded by its threshold. -/
theorem hinge_average_concentration
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) (Y : Fin m → Ω → ℝ)
    (hindep : iIndepFun Y μ) (hYm : ∀ i, AEMeasurable (Y i) μ)
    (hY : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Y i ω)
    {t L : ℝ} (ht : 0 ≤ t) (htL : t ≤ L) (hL : 0 < L)
    {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | η < |(∑ i, (hinge t (Y i ω) - ∫ x, hinge t (Y i x) ∂μ)) / m|} ≤
      2 * Real.exp (-2 * m * η ^ 2 / L ^ 2) := by
  apply bounded_average_concentration hm
  · exact hindep.comp (fun _ y ↦ hinge t y) (fun _ ↦ by unfold hinge; fun_prop)
  · intro i
    exact (measurable_const.sub measurable_id).max measurable_const |>.comp_aemeasurable (hYm i)
  · exact hL
  · intro i
    filter_upwards [hY i] with ω hω
    exact ⟨hinge_nonneg _ _, max_le (by linarith) (ht.trans htL)⟩
  · exact hη

/-- The same grid union bound serves Hoeffding in IE-21 and the eventual
Chebyshev argument in IE-22. Outer probabilities avoid extra measurable-supremum
machinery for the uncountable threshold interval. -/
theorem uniform_threshold_concentration_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L ρ η p : ℝ} (hL : 0 ≤ L) (hρ : 0 < ρ) (hp : 0 ≤ p)
    (f : Ω → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ ω, ∀ s ∈ Set.Icc 0 L, ∀ t ∈ Set.Icc 0 L, |f ω s - f ω t| ≤ |s - t|)
    (hg : ∀ s ∈ Set.Icc 0 L, ∀ t ∈ Set.Icc 0 L, |g s - g t| ≤ |s - t|)
    (hpoint : ∀ t ∈ Set.Icc 0 L, μ.real {ω | η < |f ω t - g t|} ≤ p) :
    μ.real {ω | ∃ t ∈ Set.Icc 0 L, η + 2 * ρ < |f ω t - g t|} ≤ (L / ρ + 1) * p := by
  obtain ⟨T, hT, hcard, hcover⟩ := exists_threshold_grid hL hρ
  have hsub : {ω | ∃ t ∈ Set.Icc 0 L, η + 2 * ρ < |f ω t - g t|} ⊆
      ⋃ s ∈ T, {ω | η < |f ω s - g s|} := by
    rintro ω ⟨t, ht, hbad⟩
    by_contra h
    have hgrid : ∀ s ∈ T, |f ω s - g s| ≤ η := by
      intro s hs
      by_contra hbad'
      exact h (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, lt_of_not_ge hbad'⟩⟩)
    exact (not_le_of_gt hbad) (abs_sub_le_of_threshold_grid hT hcover (hf ω) hg hgrid ht)
  calc
    _ ≤ μ.real (⋃ s ∈ T, {ω | η < |f ω s - g s|}) :=
      measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ s ∈ T, μ.real {ω | η < |f ω s - g s|} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ T, p := Finset.sum_le_sum fun s hs ↦ hpoint s (hT s hs)
    _ = (T.card : ℝ) * p := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hp

end NLA.RowDeletion

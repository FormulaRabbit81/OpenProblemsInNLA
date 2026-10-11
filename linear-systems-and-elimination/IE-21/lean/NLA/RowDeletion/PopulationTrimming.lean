import NLA.RowDeletion.Trimming
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Population trimming and its coupling estimate

The hinge supremum needs only integrability. Its stability follows from the
pointwise 1-Lipschitz hinge bound; no conditional expectation or quantile
selector is introduced.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NLA.RowDeletion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y Z : Ω → ℝ}

lemma integrable_hinge (hY : Integrable Y μ) (t : ℝ) :
    Integrable (fun ω ↦ hinge t (Y ω)) μ := by
  have he : (fun ω ↦ hinge t (Y ω)) = fun ω ↦ ((t - Y ω) + |t - Y ω|) / 2 := by
    funext ω
    rcases le_total 0 (t - Y ω) with h | h
    · rw [hinge, max_eq_left h, abs_of_nonneg h]
      ring
    · rw [hinge, max_eq_right h, abs_of_nonpos h]
      ring
  rw [he]
  exact (((integrable_const t).sub hY).add ((integrable_const t).sub hY).abs).div_const 2

lemma populationThreshold_le_mean (hY : Integrable Y μ) {θ t : ℝ}
    (hθ : θ ≤ 1) (ht : 0 ≤ t) : populationThreshold μ θ Y t ≤ ∫ ω, Y ω ∂μ := by
  have hi := integral_mono ((integrable_const t).sub hY) (integrable_hinge hY t)
    (fun ω ↦ sub_le_hinge t (Y ω))
  change (∫ ω, t - Y ω ∂μ) ≤ ∫ ω, hinge t (Y ω) ∂μ at hi
  rw [integral_sub (integrable_const t) hY] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hmul := mul_le_mul_of_nonneg_right hθ ht
  unfold populationThreshold
  linarith

lemma populationThreshold_bddAbove (hY : Integrable Y μ) {θ : ℝ} (hθ : θ ≤ 1) :
    BddAbove (populationThreshold μ θ Y '' Set.Ici 0) := by
  refine ⟨∫ ω, Y ω ∂μ, ?_⟩
  rintro v ⟨t, ht, rfl⟩
  exact populationThreshold_le_mean hY hθ ht

theorem abs_populationThreshold_sub_threshold_le (hY : Integrable Y μ)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (s t : ℝ) :
    |populationThreshold μ θ Y s - populationThreshold μ θ Y t| ≤ |s - t| := by
  suffices h : ∀ s t : ℝ, s ≤ t →
      |populationThreshold μ θ Y t - populationThreshold μ θ Y s| ≤ t - s by
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm (populationThreshold μ θ Y s), abs_sub_comm s t,
        abs_of_nonneg (sub_nonneg.mpr hst)]
      exact h s t hst
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact h t s hts
  intro s t hst
  have hdiff : Integrable (fun ω ↦ hinge t (Y ω) - hinge s (Y ω)) μ :=
    (integrable_hinge hY t).sub (integrable_hinge hY s)
  have hlo : 0 ≤ ∫ ω, hinge t (Y ω) - hinge s (Y ω) ∂μ :=
    integral_nonneg fun ω ↦ sub_nonneg.mpr (max_le_max (sub_le_sub_right hst _) le_rfl)
  have hhi : (∫ ω, hinge t (Y ω) - hinge s (Y ω) ∂μ) ≤ t - s := by
    have hi := integral_mono hdiff (integrable_const (t - s)) (fun ω ↦
      (le_abs_self _).trans ((abs_hinge_sub_hinge_left t s (Y ω)).trans_eq
        (abs_of_nonneg (sub_nonneg.mpr hst))))
    simpa only [integral_const, probReal_univ, one_smul] using hi
  rw [integral_sub (integrable_hinge hY t) (integrable_hinge hY s)] at hlo hhi
  unfold populationThreshold
  have hθlo := mul_nonneg hθ₀ (sub_nonneg.mpr hst)
  have hθhi := mul_le_mul_of_nonneg_right hθ₁ (sub_nonneg.mpr hst)
  apply abs_le.mpr
  constructor <;> nlinarith

omit [IsProbabilityMeasure μ] in
lemma populationThreshold_zero (hY : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (θ : ℝ) :
    populationThreshold μ θ Y 0 = 0 := by
  have h : (fun ω ↦ hinge 0 (Y ω)) =ᵐ[μ] fun _ ↦ 0 :=
    hY.mono fun _ h ↦ hinge_eq_zero h
  simp [populationThreshold, integral_congr_ae h]

theorem populationTrimmedMoment_nonneg (hY : Integrable Y μ)
    (hY₀ : ∀ᵐ ω ∂μ, 0 ≤ Y ω) {θ : ℝ} (hθ : θ ≤ 1) :
    0 ≤ populationTrimmedMoment μ θ Y := by
  unfold populationTrimmedMoment
  apply le_csSup (populationThreshold_bddAbove hY hθ)
  exact ⟨0, Set.mem_Ici.mpr le_rfl, populationThreshold_zero hY₀ θ⟩

theorem populationTrimmedMoment_le_mean (hY : Integrable Y μ)
    {θ : ℝ} (hθ : θ ≤ 1) : populationTrimmedMoment μ θ Y ≤ ∫ ω, Y ω ∂μ := by
  unfold populationTrimmedMoment
  have hne : (populationThreshold μ θ Y '' Set.Ici 0).Nonempty :=
    ⟨populationThreshold μ θ Y 0, 0, Set.mem_Ici.mpr le_rfl, rfl⟩
  apply csSup_le hne
  rintro v ⟨t, ht, rfl⟩
  exact populationThreshold_le_mean hY hθ ht

lemma abs_populationThreshold_sub_le (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (θ t : ℝ) :
    |populationThreshold μ θ Y t - populationThreshold μ θ Z t| ≤
      ∫ ω, |Y ω - Z ω| ∂μ := by
  have hi : Integrable (fun ω ↦ hinge t (Y ω) - hinge t (Z ω)) μ :=
    (integrable_hinge hY t).sub (integrable_hinge hZ t)
  have h := (abs_integral_le_integral_abs (f := fun ω ↦ hinge t (Y ω) - hinge t (Z ω))).trans
    (integral_mono hi.abs (hY.sub hZ).abs (fun ω ↦ abs_hinge_sub_hinge_right t (Y ω) (Z ω)))
  rw [integral_sub (integrable_hinge hY t) (integrable_hinge hZ t)] at h
  simpa only [populationThreshold, sub_sub_sub_cancel_left, abs_sub_comm, Pi.sub_apply] using h

lemma populationTrimmedMoment_le_add_coupling (hY : Integrable Y μ) (hZ : Integrable Z μ)
    {θ : ℝ} (hθ : θ ≤ 1) :
    populationTrimmedMoment μ θ Y ≤ populationTrimmedMoment μ θ Z +
      ∫ ω, |Y ω - Z ω| ∂μ := by
  unfold populationTrimmedMoment
  have hne : (populationThreshold μ θ Y '' Set.Ici 0).Nonempty :=
    ⟨populationThreshold μ θ Y 0, 0, Set.mem_Ici.mpr le_rfl, rfl⟩
  apply csSup_le hne
  rintro v ⟨t, ht, rfl⟩
  have h := (abs_le.mp (abs_populationThreshold_sub_le hY hZ θ t)).2
  have hz : populationThreshold μ θ Z t ≤ populationTrimmedMoment μ θ Z :=
    le_csSup (populationThreshold_bddAbove hZ hθ) ⟨t, ht, rfl⟩
  unfold populationTrimmedMoment at hz
  linarith

/-- Stability under any coupling, without introducing conditional selectors. -/
theorem abs_populationTrimmedMoment_sub_le (hY : Integrable Y μ) (hZ : Integrable Z μ)
    {θ : ℝ} (hθ : θ ≤ 1) :
    |populationTrimmedMoment μ θ Y - populationTrimmedMoment μ θ Z| ≤
      ∫ ω, |Y ω - Z ω| ∂μ := by
  have h₁ := populationTrimmedMoment_le_add_coupling hY hZ hθ
  have h₂ := populationTrimmedMoment_le_add_coupling hZ hY hθ
  simp only [abs_sub_comm (Z _)] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A fixed measurable set of the right mass bounds every threshold objective. -/
lemma populationThreshold_le_setIntegral (hY : Integrable Y μ)
    {s : Set Ω} (hs : MeasurableSet s) {θ : ℝ} (hmass : μ.real s = θ) (t : ℝ) :
    populationThreshold μ θ Y t ≤ ∫ ω in s, Y ω ∂μ := by
  have hind : Integrable (s.indicator (fun ω ↦ t - Y ω)) μ :=
    ((integrable_const t).sub hY).indicator hs
  have hi := integral_mono hind (integrable_hinge hY t) (fun ω ↦ by
    by_cases hω : ω ∈ s
    · simpa only [Set.indicator_of_mem hω] using sub_le_hinge t (Y ω)
    · simpa only [Set.indicator_of_notMem hω] using hinge_nonneg t (Y ω))
  rw [integral_indicator hs,
    integral_sub (integrable_const t) hY.integrableOn] at hi
  simp only [setIntegral_const, smul_eq_mul, hmass] at hi
  unfold populationThreshold
  linarith

/-- At a cutoff carrying exactly the prescribed mass, the population supremum
is the truncated first moment. No general quantile construction is needed. -/
theorem populationTrimmedMoment_eq_setIntegral (hYm : Measurable Y)
    (hY : Integrable Y μ) {θ b : ℝ} (hb : 0 ≤ b)
    (hmass : μ.real {ω | Y ω ≤ b} = θ) :
    populationTrimmedMoment μ θ Y = ∫ ω in {ω | Y ω ≤ b}, Y ω ∂μ := by
  let s : Set Ω := {ω | Y ω ≤ b}
  have hs : MeasurableSet s := measurableSet_le hYm measurable_const
  have hfun : (fun ω ↦ hinge b (Y ω)) = s.indicator (fun ω ↦ b - Y ω) := by
    funext ω
    by_cases hω : Y ω ≤ b
    · rw [Set.indicator_of_mem (show ω ∈ s from hω), hinge_eq_sub hω]
    · rw [Set.indicator_of_notMem (show ω ∉ s from hω), hinge_eq_zero (le_of_not_ge hω)]
  have heq : populationThreshold μ θ Y b = ∫ ω in s, Y ω ∂μ := by
    unfold populationThreshold
    rw [hfun, integral_indicator hs, integral_sub (integrable_const b) hY.integrableOn]
    simp only [setIntegral_const, smul_eq_mul, show μ.real s = θ from hmass]
    ring
  have hupper : ∀ v ∈ populationThreshold μ θ Y '' Set.Ici 0,
      v ≤ ∫ ω in s, Y ω ∂μ := by
    rintro v ⟨t, _, rfl⟩
    exact populationThreshold_le_setIntegral hY hs hmass t
  unfold populationTrimmedMoment
  apply le_antisymm
  · exact csSup_le ⟨populationThreshold μ θ Y b, b, hb, rfl⟩ hupper
  · exact le_csSup ⟨_, hupper⟩ ⟨b, hb, heq⟩

end NLA.RowDeletion

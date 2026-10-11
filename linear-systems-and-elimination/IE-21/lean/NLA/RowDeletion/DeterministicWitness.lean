import NLA.RowDeletion.Variational
import NLA.RowDeletion.Sphere
import NLA.RowDeletion.GaussianTrimming

/-! # Extracting deterministic unit-row witnesses from concentration

This is the shared step from IE-21 to the lower bound and sharpness in IE-22.
It uses the specified spherical law and does not require measurability of the
bad event: an outer-probability bound strictly below one already suffices.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace NLA.RowDeletion

theorem exists_good_not_bad
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {good bad : Ω → Prop} (hgood : ∀ᵐ ω ∂μ, good ω)
    (hbad : μ.real {ω | bad ω} < 1) : ∃ ω, good ω ∧ ¬bad ω := by
  by_contra h
  have hb : ∀ᵐ ω ∂μ, bad ω := hgood.mono fun ω hω ↦ by
    by_contra hn
    exact h ⟨ω, hω, hn⟩
  have hm : μ Set.univ ≤ μ {ω | bad ω} :=
    measure_mono_ae (hb.mono fun _ hω _ ↦ hω)
  have hr := ENNReal.toReal_mono (measure_ne_top μ {ω | bad ω}) hm
  simp only [measure_univ, ENNReal.toReal_one] at hr
  exact (not_le_of_gt hbad) hr

theorem exists_unitRows_large_of_bad_probability_lt_one
    {m n : ℕ} (hn : 0 < n) {θ h c ε : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hc : 0 ≤ c) (hgap : c ^ 2 + ε < h)
    (hbad : (sphericalRowsLaw m n).real
      {A | ε < |normalizedTrimmedEnergy θ A - h|} < 1) :
    ∃ A : Rows m n, UnitRows A ∧ c < normalizedDeletion θ A := by
  let := isProbabilityMeasure_sphericalRowsLaw m hn
  obtain ⟨A, hA, he⟩ := exists_good_not_bad (ae_sphericalRowsLaw_unitRows m hn) hbad
  have hs := (abs_le.mp (le_of_not_gt he)).1
  have hsq := normalizedDeletion_sq hn hθ₀ hθ₁ A
  have hnonneg := normalizedDeletion_nonneg hn hθ₁ A
  refine ⟨A, hA, ?_⟩
  nlinarith

/-- Any concentration result for the squared normalization immediately gives
deterministic realizations exceeding every smaller nonnegative constant. -/
theorem eventually_exists_unitRows_large_of_concentration
    {θ h c : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hc : 0 ≤ c)
    (hgap : c ^ 2 < h) (m n : ℕ → ℕ) (hn : ∀ j, 0 < n j)
    (hconcentration : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun j ↦ (sphericalRowsLaw (m j) (n j)).real
        {A | ε < |normalizedTrimmedEnergy θ A - h|}) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∃ A : Rows (m j) (n j), UnitRows A ∧ c < normalizedDeletion θ A := by
  have hε : 0 < (h - c ^ 2) / 2 := by linarith
  filter_upwards [(hconcentration _ hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with j hj
  exact exists_unitRows_large_of_bad_probability_lt_one (hn j) hθ₀ hθ₁ hc (by linarith) hj

end NLA.RowDeletion

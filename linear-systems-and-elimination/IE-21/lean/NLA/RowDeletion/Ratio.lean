import NLA.RowDeletion.Variational
import NLA.RowDeletion.Sphere

/-! # Transferring the two normalized limits to the original ratio

The argument works with a different probability space at every index. A direct
bad-event inclusion avoids imposing a common ambient space or invoking a
version of convergence in probability with the wrong quantifiers.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace NLA.RowDeletion

theorem deletionRatio_eq_normalized_ratio {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (A : Rows m n) :
    deletionRatio θ A = normalizedTrimmedEnergy θ A / normalizedOperatorEnergy A := by
  unfold deletionRatio normalizedTrimmedEnergy normalizedOperatorEnergy
  rw [deletionSingularValue_sq hn hθ₀ hθ₁]
  have hs : (n : ℝ) / m ≠ 0 := div_ne_zero (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')
  exact (mul_div_mul_left _ _ hs).symm

lemma abs_ratio_sub_le {E O h d t : ℝ} (hE : |E - h| ≤ d) (hO : |O - 1| ≤ t)
    (hh : |h| ≤ 1) (ht : t < 1) : |E / O - h| ≤ (d + t) / (1 - t) := by
  have ht₀ : 0 ≤ t := (abs_nonneg _).trans hO
  have hd₀ : 0 ≤ d := (abs_nonneg _).trans hE
  have hOlo : 1 - t ≤ O := by have := (abs_le.mp hO).1; linarith
  have hOpos : 0 < O := by linarith
  have heq : E / O - h = ((E - h) + h * (1 - O)) / O := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hOpos]
  have hnum : |(E - h) + h * (1 - O)| ≤ d + t := by
    calc
      _ ≤ |E - h| + |h * (1 - O)| := abs_add_le _ _
      _ ≤ d + 1 * t := by
        rw [abs_mul, abs_sub_comm 1 O]
        exact add_le_add hE (mul_le_mul hh hO (abs_nonneg _) (by norm_num))
      _ = d + t := by ring
  exact (div_le_div_of_nonneg_right hnum hOpos.le).trans
    (div_le_div_of_nonneg_left (by linarith) (by linarith) hOlo)

/-- Slutsky's ratio step for varying probability spaces, using outer probabilities. -/
theorem ratio_concentration_of_concentration
    {Ω : ℕ → Type*} [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (E O : ∀ j, Ω j → ℝ) {h : ℝ} (hh : |h| ≤ 1)
    (hE : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun j ↦ (μ j).real {ω | ε < |E j ω - h|}) atTop (𝓝 0))
    (hO : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun j ↦ (μ j).real {ω | ε < |O j ω - 1|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun j ↦ (μ j).real {ω | ε < |E j ω / O j ω - h|}) atTop (𝓝 0) := by
  let δ := min (1 / 2 : ℝ) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hbound (j : ℕ) : (μ j).real {ω | ε < |E j ω / O j ω - h|} ≤
      (μ j).real {ω | δ < |E j ω - h|} + (μ j).real {ω | δ < |O j ω - 1|} := by
    apply le_trans (measureReal_mono (show {ω | ε < |E j ω / O j ω - h|} ⊆
      {ω | δ < |E j ω - h|} ∪ {ω | δ < |O j ω - 1|} from ?_))
      (measureReal_union_le _ _)
    intro ω hω
    by_contra hn
    have hn' : |E j ω - h| ≤ δ ∧ |O j ω - 1| ≤ δ := by
      simpa only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] using hn
    have hr := abs_ratio_sub_le hn'.1 hn'.2 hh (by linarith : δ < 1)
    have hb : (δ + δ) / (1 - δ) ≤ ε := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).mpr
      have := mul_le_mul_of_nonneg_left hδhalf hε.le
      nlinarith
    exact (not_le_of_gt hω) (hr.trans hb)
  exact squeeze_zero (fun _ ↦ measureReal_nonneg) hbound
    (by simpa using (hE δ hδ).add (hO δ hδ))

theorem deletionRatio_tendsto_of_concentration
    {θ h : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hh : |h| ≤ 1)
    (m n : ℕ → ℕ) (hdim : ∀ j, 0 < m j ∧ 0 < n j)
    (htrim : ∀ ε : ℝ, 0 < ε → Tendsto (fun j ↦ (sphericalRowsLaw (m j) (n j)).real
      {A | ε < |normalizedTrimmedEnergy θ A - h|}) atTop (𝓝 0))
    (hop : ∀ ε : ℝ, 0 < ε → Tendsto (fun j ↦ (sphericalRowsLaw (m j) (n j)).real
      {A | ε < |normalizedOperatorEnergy A - 1|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun j ↦ (sphericalRowsLaw (m j) (n j)).real
      {A | ε < |deletionRatio θ A - h|}) atTop (𝓝 0) := by
  let : ∀ j, IsProbabilityMeasure (sphericalRowsLaw (m j) (n j)) :=
    fun j ↦ isProbabilityMeasure_sphericalRowsLaw (m j) (hdim j).2
  simpa only [deletionRatio_eq_normalized_ratio (hdim _).1 (hdim _).2 hθ₀ hθ₁] using
    ratio_concentration_of_concentration (fun j ↦ sphericalRowsLaw (m j) (n j))
      (fun _ ↦ normalizedTrimmedEnergy θ) (fun _ ↦ normalizedOperatorEnergy) hh htrim hop hε

end NLA.RowDeletion

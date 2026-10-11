import NLA.RowDeletion.PopulationTrimming
import NLA.RowDeletion.Gaussian

/-! # Identifying the population threshold constant with the canonical Gaussian integral -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.RowDeletion

lemma integrable_gaussian_sq : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal 2).integrable_sq

lemma integral_gaussian_sq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  simpa using h.symm

lemma square_sublevel_eq_interval {a : ℝ} (ha : 0 ≤ a) :
    {x : ℝ | x ^ 2 ≤ a ^ 2} = Set.Icc (-a) a := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨hl, hu⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ a + x by linarith)]

theorem populationTrimmedMoment_gaussian {θ a : ℝ} (ha : GaussianCutoff θ a) :
    populationTrimmedMoment (gaussianReal 0 1) θ (fun x : ℝ ↦ x ^ 2) =
      gaussianTrimmedMoment a := by
  have he := square_sublevel_eq_interval ha.1.le
  have h := populationTrimmedMoment_eq_setIntegral
    (μ := gaussianReal 0 1) (Y := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    integrable_gaussian_sq (sq_nonneg a) (by simpa only [he] using ha.2)
  simpa only [he, gaussianTrimmedMoment] using h

theorem gaussianTrimmedMoment_nonneg (a : ℝ) : 0 ≤ gaussianTrimmedMoment a :=
  integral_nonneg fun x ↦ sq_nonneg x

/-- Agreement with the canonical Gaussian density integral. -/
theorem gaussianTrimmedMoment_eq_density_integral (a : ℝ) :
    gaussianTrimmedMoment a =
      ∫ x in Set.Icc (-a) a, x ^ 2 * gaussianPDFReal 0 1 x := by
  unfold gaussianTrimmedMoment
  rw [← integral_indicator measurableSet_Icc,
    integral_gaussianReal_eq_integral_smul one_ne_zero,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (-a) a <;> simp [hx, mul_comm]

theorem gaussianTrimmedMoment_le_one {θ a : ℝ} (hθ : θ ≤ 1)
    (ha : GaussianCutoff θ a) : gaussianTrimmedMoment a ≤ 1 := by
  rw [← populationTrimmedMoment_gaussian ha, ← integral_gaussian_sq]
  exact populationTrimmedMoment_le_mean integrable_gaussian_sq hθ

end NLA.RowDeletion

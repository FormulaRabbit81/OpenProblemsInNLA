/-
One-dimensional Gaussian interval bounds for the first branch of Lemma 3.6.

Conditioned on the radial and phase coordinates, the source proof bounds a
real Gaussian interval by its peak density.  This module records that exact
analytic input independently of the remaining planted-law disintegration.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section

namespace NLA.FR05

theorem gaussianPDFReal_le_peak (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  rw [gaussianPDFReal]
  have harg : -(x - μ) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · positivity
  have hexp : Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr harg
  simpa using
    (mul_le_mul_of_nonneg_left hexp
      (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * (v : ℝ)))))

theorem gaussianPDF_le_peak (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDF μ v x ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  change ENNReal.ofReal (gaussianPDFReal μ v x) ≤ _
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_peak μ v x)

theorem gaussianReal_set_le_peak (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (s : Set ℝ) :
    gaussianReal μ v s ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * volume s := by
  rw [gaussianReal_apply μ hv s]
  calc
    ∫⁻ x in s, gaussianPDF μ v x ≤
        ∫⁻ _ in s, ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ :=
      lintegral_mono fun x ↦ gaussianPDF_le_peak μ v x
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * volume s :=
      setLIntegral_const s _

theorem gaussianReal_Icc_smallBall (μ a u : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u / Real.sqrt (2 * Real.pi * (v : ℝ))) := by
  calc
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
        ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          volume (Set.Icc (a - u) (a + u)) :=
      gaussianReal_set_le_peak μ hv _
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          ENNReal.ofReal (2 * u) := by
      rw [Real.volume_Icc]
      congr 2
      ring
    _ = ENNReal.ofReal (2 * u / Real.sqrt (2 * Real.pi * (v : ℝ))) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      congr 1
      ring

theorem gaussianReal_Icc_smallBall_of_sq_le (μ a u r : ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) (hu : 0 ≤ u) (hr : 0 < r) (hvar : r ^ 2 ≤ (v : ℝ)) :
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u / (Real.sqrt (2 * Real.pi) * r)) := by
  have htwo_pi : 0 < 2 * Real.pi := by positivity
  have hroot : r ≤ Real.sqrt (v : ℝ) := by
    exact (Real.le_sqrt hr.le (NNReal.zero_le_coe)).mpr hvar
  have hden : Real.sqrt (2 * Real.pi) * r ≤
      Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    rw [Real.sqrt_mul htwo_pi.le]
    exact mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
  have hdenpos : 0 < Real.sqrt (2 * Real.pi) * r :=
    mul_pos (Real.sqrt_pos.2 htwo_pi) hr
  have hratio : 2 * u / Real.sqrt (2 * Real.pi * (v : ℝ)) ≤
      2 * u / (Real.sqrt (2 * Real.pi) * r) := by
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hu) hdenpos hden
  exact (gaussianReal_Icc_smallBall μ a u hv).trans
    (ENNReal.ofReal_le_ofReal hratio)

theorem gaussianReal_Icc_smallBall_of_scaled_sq_le
    (μ a u t S : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hu : 0 ≤ u)
    (ht : 0 < t) (hS : 0 < S)
    (hvar : (t / Real.sqrt S) ^ 2 ≤ (v : ℝ)) :
    gaussianReal μ v (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) := by
  have hsqrtS : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hr : 0 < t / Real.sqrt S := div_pos ht hsqrtS
  have hsmall := gaussianReal_Icc_smallBall_of_sq_le μ a u
    (t / Real.sqrt S) hv hu hr hvar
  have heq :
      2 * u / (Real.sqrt (2 * Real.pi) * (t / Real.sqrt S)) =
        2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t) := by
    field_simp [hsqrtS.ne', ht.ne']
  simpa only [heq] using hsmall

/-- The source-ready form: if the unscaled variance `V` is at least `t²`,
then a Gaussian of variance `V / S` has the stated interval small-ball bound. -/
theorem gaussianReal_Icc_smallBall_of_real_variance
    (μ a u t V S : ℝ) (hu : 0 ≤ u) (ht : 0 < t) (hS : 0 < S)
    (hV : t ^ 2 ≤ V) :
    gaussianReal μ ⟨V / S, div_nonneg (le_trans (sq_nonneg t) hV) hS.le⟩
        (Set.Icc (a - u) (a + u)) ≤
      ENNReal.ofReal (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) := by
  let v : ℝ≥0 := ⟨V / S, div_nonneg (le_trans (sq_nonneg t) hV) hS.le⟩
  have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hVpos : 0 < V := lt_of_lt_of_le htSq hV
  have hv : v ≠ 0 := by
    exact ne_of_gt (by
      change 0 < V / S
      exact div_pos hVpos hS)
  have hvar : (t / Real.sqrt S) ^ 2 ≤ (v : ℝ) := by
    change (t / Real.sqrt S) ^ 2 ≤ V / S
    calc
      (t / Real.sqrt S) ^ 2 = t ^ 2 / S := by
        rw [div_pow, Real.sq_sqrt hS.le]
      _ ≤ V / S := div_le_div_of_nonneg_right hV hS.le
  simpa only [v] using
    (gaussianReal_Icc_smallBall_of_scaled_sq_le μ a u t S hv hu ht hS hvar)

end NLA.FR05

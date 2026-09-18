/-
Small-ball estimate for a projection under the actual complex-Gaussian tail
law.  This combines the exact law in `GaussianProjection.lean` with the
one-dimensional density estimate in `GaussianSmallBall.lean`.
-/
import NLA.FR05.GaussianProjection
import NLA.FR05.GaussianSmallBall
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace NLA.FR05

theorem signalEnergy_nonneg {n : ℕ} (z : Signal n) : 0 ≤ signalEnergy z := by
  unfold signalEnergy squaredEuclideanNorm
  exact Finset.sum_nonneg fun j hj ↦ Complex.normSq_nonneg (z j)

/-- If the real projection has variance at least `t²`, its interval
probability under the exact standard complex-Gaussian tail law is bounded by
the peak-density estimate. -/
theorem standardComplexGaussianTail_smallBall
    {n : ℕ} (z : Signal n) (a u t : ℝ)
    (hu : 0 ≤ u) (ht : 0 < t)
    (hvariance : t ^ 2 ≤ signalEnergy z / 2) :
    standardComplexGaussianTail n
        {w | |(star w ⬝ᵥ z).re - a| ≤ u} ≤
      ENNReal.ofReal (2 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let f : Signal n → ℝ := fun w ↦ (star w ⬝ᵥ z).re
  let v : ℝ≥0 := (signalEnergy z / 2).toNNReal
  have henergy : 0 ≤ signalEnergy z := signalEnergy_nonneg z
  have henergyhalf : 0 ≤ signalEnergy z / 2 := div_nonneg henergy (by norm_num)
  have hvreal : (v : ℝ) = signalEnergy z / 2 := by
    dsimp [v]
    simp [henergyhalf]
  have hvpos : 0 < (v : ℝ) := by
    rw [hvreal]
    exact lt_of_lt_of_le (sq_pos_of_pos ht) hvariance
  have hv : v ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast hvpos
  have hvar : t ^ 2 ≤ (v : ℝ) := by
    rw [hvreal]
    exact hvariance
  have hset : {w : Signal n | |f w - a| ≤ u} =
      f ⁻¹' Icc (a - u) (a + u) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
    constructor
    · intro h
      have h' := abs_sub_le_iff.mp h
      constructor <;> linarith
    · rintro ⟨hleft, hright⟩
      apply abs_sub_le_iff.mpr
      constructor <;> linarith
  calc
    standardComplexGaussianTail n {w | |(star w ⬝ᵥ z).re - a| ≤ u} =
        standardComplexGaussianTail n (f ⁻¹' Icc (a - u) (a + u)) := by
      change standardComplexGaussianTail n {w | |f w - a| ≤ u} = _
      rw [hset]
    _ = (standardComplexGaussianTail n).map f (Icc (a - u) (a + u)) := by
      rw [Measure.map_apply (measurable_real_star_dotProduct z) measurableSet_Icc]
    _ = gaussianReal 0 v (Icc (a - u) (a + u)) := by
      rw [show f = (fun w : Signal n ↦ (star w ⬝ᵥ z).re) by rfl,
        standardComplexGaussianTail_map_real_dotProduct]
    _ ≤ ENNReal.ofReal (2 * u / (Real.sqrt (2 * Real.pi) * t)) :=
      gaussianReal_Icc_smallBall_of_sq_le 0 a u t hv hu ht hvar

/-- The same interval estimate after a deterministic phase rotation of the
tail.  The rotation is transferred to the direction, where energy is
preserved, rather than appealing to an unproved invariance assertion. -/
theorem standardComplexGaussianTail_phaseRotate_smallBall
    {n : ℕ} (α : ℝ) (z : Signal n) (a u t : ℝ)
    (hu : 0 ≤ u) (ht : 0 < t)
    (hvariance : t ^ 2 ≤ signalEnergy z / 2) :
    standardComplexGaussianTail n
        {w | |(star (Complex.exp ((-α : ℂ) * Complex.I) • w) ⬝ᵥ z).re - a| ≤ u} ≤
      ENNReal.ofReal (2 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  have hset :
      {w : Signal n | |(star (Complex.exp ((-α : ℂ) * Complex.I) • w) ⬝ᵥ z).re - a| ≤ u} =
        {w : Signal n | |(star w ⬝ᵥ
          (Complex.exp ((α : ℂ) * Complex.I) • z)).re - a| ≤ u} := by
    ext w
    change |(star (Complex.exp ((-α : ℂ) * Complex.I) • w) ⬝ᵥ z).re - a| ≤ u ↔
      |(star w ⬝ᵥ (Complex.exp ((α : ℂ) * Complex.I) • z)).re - a| ≤ u
    rw [phaseRotate_real_dotProduct]
  rw [hset]
  apply standardComplexGaussianTail_smallBall
  · exact hu
  · exact ht
  · rw [signalEnergy_phaseRotate]
    exact hvariance

end NLA.FR05

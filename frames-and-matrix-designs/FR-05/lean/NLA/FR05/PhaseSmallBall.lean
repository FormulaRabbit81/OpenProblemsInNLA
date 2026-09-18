/-
The one-dimensional phase input to the Gaussian small-ball branch of Lemma 3.6.

The source phase law is normalized Lebesgue measure on `[0, 2π]`.  The
estimate below proves the sharp linear bound for the canonical cosine profile
which arises after a phase normalization.
-/
import NLA.FR05.PlantedLaw
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- Normalized Lebesgue measure on the source phase interval `[0, 2π]`. -/
def phaseUniformMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ •
    volume.restrict (Icc 0 (2 * Real.pi))

/-- The canonical quadratic cosine sublevel set on one phase period. -/
def cosinePhaseSublevel (t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ 1 + Real.cos φ ≤ t ^ 2}

/-- The source phase law is definitionally the normalized one-period law. -/
theorem sourceUniformInterval_zero_two_pi_eq_phaseUniformMeasure :
    sourceUniformInterval 0 (2 * Real.pi) = phaseUniformMeasure := by
  unfold sourceUniformInterval ProbabilityTheory.cond phaseUniformMeasure
  rw [Real.volume_Icc]
  congr 1
  ring_nf

theorem measurableSet_cosinePhaseSublevel (t : ℝ) :
    MeasurableSet (cosinePhaseSublevel t) := by
  unfold cosinePhaseSublevel
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (measurable_const.add Real.continuous_cos.measurable) measurable_const

/-- A trigonometric normal form centered at the unique zero in `[0, 2π]`. -/
theorem one_add_cos_eq_two_sin_sq_half_sub (φ : ℝ) :
    1 + Real.cos φ = 2 * Real.sin ((φ - Real.pi) / 2) ^ 2 := by
  let x : ℝ := (φ - Real.pi) / 2
  have hx : φ - Real.pi = 2 * x := by
    dsimp [x]
    ring
  calc
    1 + Real.cos φ = 1 - Real.cos (φ - Real.pi) := by
      rw [Real.cos_sub_pi]
      ring
    _ = 2 * Real.sin x ^ 2 := by
      rw [hx, Real.cos_two_mul]
      have htrig := Real.cos_sq_add_sin_sq x
      nlinarith

/-- A small canonical cosine value confines the phase to a short interval
around `π`. -/
theorem cosinePhaseSublevel_subset (t : ℝ) (ht : 0 ≤ t) :
    cosinePhaseSublevel t ⊆
      Icc (Real.pi - Real.pi * t) (Real.pi + Real.pi * t) := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ 1 + Real.cos φ ≤ t ^ 2 at hφ
  let x : ℝ := (φ - Real.pi) / 2
  have hx_lower : -(Real.pi / 2) ≤ x := by
    dsimp [x]
    linarith [hφ.1.1]
  have hx_upper : x ≤ Real.pi / 2 := by
    dsimp [x]
    linarith [hφ.1.2]
  have hxabs : |x| ≤ Real.pi / 2 := abs_le.mpr ⟨hx_lower, hx_upper⟩
  have hidentity : 1 + Real.cos φ = 2 * Real.sin x ^ 2 := by
    simpa only [x] using one_add_cos_eq_two_sin_sq_half_sub φ
  have hsin_sq : Real.sin x ^ 2 ≤ t ^ 2 := by
    change φ ∈ Icc 0 (2 * Real.pi) ∧ 1 + Real.cos φ ≤ t ^ 2 at hφ
    rw [hidentity] at hφ
    nlinarith [hφ.2, sq_nonneg (Real.sin x)]
  have hsinabs : |Real.sin x| ≤ t :=
    abs_le_of_sq_le_sq hsin_sq ht
  have hjordan : 2 / Real.pi * |x| ≤ |Real.sin x| :=
    Real.mul_abs_le_abs_sin hxabs
  have hlinear : 2 / Real.pi * |x| ≤ t := hjordan.trans hsinabs
  have hscaled := mul_le_mul_of_nonneg_left hlinear
    (show 0 ≤ Real.pi / 2 by positivity)
  have hleft : Real.pi / 2 * (2 / Real.pi * |x|) = |x| := by
    field_simp [Real.pi_ne_zero]
  have hxsmall : |x| ≤ Real.pi / 2 * t := by
    rw [hleft] at hscaled
    exact hscaled
  rcases abs_le.mp hxsmall with ⟨hlo, hhi⟩
  dsimp [x] at hlo hhi
  constructor <;> ring_nf at hlo hhi ⊢ <;> linarith

/-- Raw Lebesgue measure estimate for the one-period canonical sublevel set. -/
theorem volume_cosinePhaseSublevel_le (t : ℝ) (ht : 0 ≤ t) :
    volume (cosinePhaseSublevel t) ≤ ENNReal.ofReal (2 * Real.pi * t) := by
  calc
    volume (cosinePhaseSublevel t) ≤
        volume (Icc (Real.pi - Real.pi * t) (Real.pi + Real.pi * t)) :=
      measure_mono (cosinePhaseSublevel_subset t ht)
    _ = ENNReal.ofReal (2 * Real.pi * t) := by
      rw [Real.volume_Icc]
      congr 1
      ring

/-- Normalizing the raw estimate gives the source-faithful phase probability
bound `P(1 + cos φ ≤ t²) ≤ t`. -/
theorem phaseUniformMeasure_cosinePhaseSublevel_le (t : ℝ) (ht : 0 ≤ t) :
    phaseUniformMeasure (cosinePhaseSublevel t) ≤ ENNReal.ofReal t := by
  have hsub : cosinePhaseSublevel t ⊆ Icc 0 (2 * Real.pi) := by
    intro φ hφ
    exact hφ.1
  have hvol := volume_cosinePhaseSublevel_le t ht
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpi).ne'
  rw [phaseUniformMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (measurableSet_cosinePhaseSublevel t),
    Set.inter_eq_left.mpr hsub]
  calc
    (ENNReal.ofReal (2 * Real.pi))⁻¹ * volume (cosinePhaseSublevel t) ≤
        (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ENNReal.ofReal (2 * Real.pi * t) :=
      mul_le_mul_of_nonneg_left hvol bot_le
    _ = ENNReal.ofReal t := by
      rw [ENNReal.ofReal_mul hpi.le, ← mul_assoc,
        ENNReal.inv_mul_cancel hpi0 ENNReal.ofReal_ne_top, one_mul]

/-- The phase small-ball estimate in the exact source law notation. -/
theorem sourceUniformInterval_cosinePhaseSublevel_le (t : ℝ) (ht : 0 ≤ t) :
    sourceUniformInterval 0 (2 * Real.pi) (cosinePhaseSublevel t) ≤
      ENNReal.ofReal t := by
  rw [sourceUniformInterval_zero_two_pi_eq_phaseUniformMeasure]
  exact phaseUniformMeasure_cosinePhaseSublevel_le t ht

end NLA.FR05

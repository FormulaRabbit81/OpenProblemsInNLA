/-
Phase-shift invariance for the affine-cosine branch of Lemma 3.6.

The source variance profile is a cosine with an arbitrary phase offset.  This
module transports the interval law `sourceUniformInterval 0 (2 * π)` to the
additive circle, uses Haar invariance to remove that offset, and transports the
result back.  It therefore connects the affine estimate in `PhaseAffine` to
the source-faithful shifted profile.
-/
import NLA.FR05.PhaseAffine
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

local instance phasePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The affine cosine sublevel set on the additive phase circle. -/
def angleAffineCosineSublevel (A B t : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | A + B * Real.Angle.cos θ ≤ t ^ 2}

/-- The circular affine sublevel set after an additive phase shift. -/
def shiftedAngleAffineCosineSublevel (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | A + B * Real.Angle.cos (δ + θ) ≤ t ^ 2}

/-- The shifted affine profile written on the original real source interval. -/
def shiftedAffineCosinePhaseSublevel (δ A B t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧
    A + B * Real.cos (δ + φ) ≤ t ^ 2}

/-- Normalized Haar measure on the phase circle. -/
def phaseCircleMeasure : Measure (AddCircle (2 * Real.pi)) :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume

theorem measurableSet_angleAffineCosineSublevel (A B t : ℝ) :
    MeasurableSet (angleAffineCosineSublevel A B t) := by
  unfold angleAffineCosineSublevel
  have hcos : Measurable
      (fun θ : AddCircle (2 * Real.pi) => Real.Angle.cos θ) := by
    apply Continuous.measurable
    exact Real.Angle.continuous_cos
  exact measurableSet_le
    (measurable_const.add (measurable_const.mul hcos))
    measurable_const

theorem shiftedAngleAffineCosineSublevel_eq_preimage
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    shiftedAngleAffineCosineSublevel δ A B t =
      (fun θ : AddCircle (2 * Real.pi) => δ + θ) ⁻¹'
        angleAffineCosineSublevel A B t := by
  rfl

theorem measurableSet_shiftedAngleAffineCosineSublevel
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    MeasurableSet (shiftedAngleAffineCosineSublevel δ A B t) := by
  rw [shiftedAngleAffineCosineSublevel_eq_preimage]
  exact (measurableSet_angleAffineCosineSublevel A B t).preimage
    (measurePreserving_add_left volume δ).measurable

/-- Haar invariance removes an arbitrary additive phase shift. -/
theorem volume_shiftedAngleAffineCosineSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    volume (shiftedAngleAffineCosineSublevel δ A B t) =
      volume (angleAffineCosineSublevel A B t) := by
  rw [shiftedAngleAffineCosineSublevel_eq_preimage]
  exact (measurePreserving_add_left volume δ).measure_preimage
    (measurableSet_angleAffineCosineSublevel A B t).nullMeasurableSet

theorem volume_angleAffineCosineSublevel_eq_volume_affineCosinePhaseSublevel
    (A B t : ℝ) :
    volume (angleAffineCosineSublevel A B t) =
      volume (affineCosinePhaseSublevel A B t) := by
  let coeAngle : ℝ → AddCircle (2 * Real.pi) := fun x => (x : Real.Angle)
  have hpremeas : MeasurableSet (coeAngle ⁻¹' angleAffineCosineSublevel A B t) :=
    (measurableSet_angleAffineCosineSublevel A B t).preimage
      AddCircle.measurable_mk'
  have hmeasure := (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measure_preimage
    (measurableSet_angleAffineCosineSublevel A B t).nullMeasurableSet
  have hrestrict : volume.restrict (Ioc 0 (2 * Real.pi)) =
      volume.restrict (Icc 0 (2 * Real.pi)) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  calc
    volume (angleAffineCosineSublevel A B t) =
        (volume.restrict (Ioc 0 (2 * Real.pi)))
          (coeAngle ⁻¹' angleAffineCosineSublevel A B t) := by
      simpa [coeAngle, Real.Angle.coe] using hmeasure.symm
    _ = (volume.restrict (Icc 0 (2 * Real.pi)))
          (coeAngle ⁻¹' angleAffineCosineSublevel A B t) := by rw [hrestrict]
    _ = volume (affineCosinePhaseSublevel A B t) := by
      rw [Measure.restrict_apply hpremeas]
      congr 1
      ext φ
      simp only [Set.mem_inter_iff, coeAngle,
        angleAffineCosineSublevel, affineCosinePhaseSublevel]
      constructor <;> intro h
      · exact ⟨h.2, h.1⟩
      · exact ⟨h.2, h.1⟩

theorem measurableSet_affineCosinePhaseSublevel (A B t : ℝ) :
    MeasurableSet (affineCosinePhaseSublevel A B t) := by
  unfold affineCosinePhaseSublevel
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (measurable_const.add (measurable_const.mul Real.continuous_cos.measurable))
    measurable_const

theorem measurableSet_shiftedAffineCosinePhaseSublevel (δ A B t : ℝ) :
    MeasurableSet (shiftedAffineCosinePhaseSublevel δ A B t) := by
  unfold shiftedAffineCosinePhaseSublevel
  apply measurableSet_Icc.inter
  have hcos : Measurable (fun φ : ℝ => Real.cos (δ + φ)) := by
    fun_prop
  exact measurableSet_le (measurable_const.add (measurable_const.mul hcos))
    measurable_const

theorem sourceUniformInterval_affineCosinePhaseSublevel_eq_phaseCircleMeasure
    (A B t : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) =
      phaseCircleMeasure (angleAffineCosineSublevel A B t) := by
  have hsub : affineCosinePhaseSublevel A B t ⊆ Icc 0 (2 * Real.pi) := by
    intro φ hφ
    exact hφ.1
  unfold sourceUniformInterval ProbabilityTheory.cond phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc,
    Measure.restrict_apply (measurableSet_affineCosinePhaseSublevel A B t),
    Set.inter_eq_left.mpr hsub, Measure.smul_apply, smul_eq_mul,
    volume_angleAffineCosineSublevel_eq_volume_affineCosinePhaseSublevel]
  congr 1
  ring_nf

theorem sourceUniformInterval_shiftedAffineCosinePhaseSublevel_eq_phaseCircleMeasure
    (δ A B t : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedAffineCosinePhaseSublevel δ A B t) =
      phaseCircleMeasure
        (shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) := by
  have hsub : shiftedAffineCosinePhaseSublevel δ A B t ⊆ Icc 0 (2 * Real.pi) := by
    intro φ hφ
    exact hφ.1
  let coeAngle : ℝ → AddCircle (2 * Real.pi) := fun x => (x : Real.Angle)
  have hpremeas : MeasurableSet
      (coeAngle ⁻¹' shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) :=
    (measurableSet_shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t).preimage
      AddCircle.measurable_mk'
  have hmeasure := (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measure_preimage
    (measurableSet_shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t).nullMeasurableSet
  have hrestrict : volume.restrict (Ioc 0 (2 * Real.pi)) =
      volume.restrict (Icc 0 (2 * Real.pi)) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  unfold sourceUniformInterval ProbabilityTheory.cond phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc,
    Measure.restrict_apply (measurableSet_shiftedAffineCosinePhaseSublevel δ A B t),
    Set.inter_eq_left.mpr hsub, Measure.smul_apply, smul_eq_mul]
  have hvolume : volume
      (shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) =
      volume (shiftedAffineCosinePhaseSublevel δ A B t) := by
    calc
      volume (shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) =
          (volume.restrict (Ioc 0 (2 * Real.pi)))
            (coeAngle ⁻¹' shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) := by
        simpa [coeAngle, Real.Angle.coe] using hmeasure.symm
      _ = (volume.restrict (Icc 0 (2 * Real.pi)))
            (coeAngle ⁻¹' shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) := by
        rw [hrestrict]
      _ = volume (shiftedAffineCosinePhaseSublevel δ A B t) := by
        rw [Measure.restrict_apply hpremeas]
        congr 1
        ext φ
        simp only [Set.mem_inter_iff, coeAngle,
          shiftedAngleAffineCosineSublevel, shiftedAffineCosinePhaseSublevel]
        constructor <;> intro h
        · exact ⟨h.2, h.1⟩
        · exact ⟨h.2, h.1⟩
  rw [hvolume]
  congr 1
  ring_nf

theorem phaseCircleMeasure_shiftedAngleAffineCosineSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    phaseCircleMeasure (shiftedAngleAffineCosineSublevel δ A B t) =
      phaseCircleMeasure (angleAffineCosineSublevel A B t) := by
  unfold phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul,
    volume_shiftedAngleAffineCosineSublevel_eq]

theorem phaseCircleMeasure_angleAffineCosineSublevel_le_four_mul_of_quarter
    (A B t : ℝ) (ht : 0 ≤ t) (hA : (1 / 4 : ℝ) ≤ A)
    (hB : 0 ≤ B) (hBA : B ≤ A) :
    phaseCircleMeasure (angleAffineCosineSublevel A B t) ≤
      ENNReal.ofReal (4 * t) := by
  rw [← sourceUniformInterval_affineCosinePhaseSublevel_eq_phaseCircleMeasure]
  exact sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul_of_quarter
    A B t ht hA hB hBA

theorem phaseCircleMeasure_shiftedAngleAffineCosineSublevel_le_four_mul_of_quarter
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) (ht : 0 ≤ t)
    (hA : (1 / 4 : ℝ) ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) :
    phaseCircleMeasure (shiftedAngleAffineCosineSublevel δ A B t) ≤
      ENNReal.ofReal (4 * t) := by
  rw [phaseCircleMeasure_shiftedAngleAffineCosineSublevel_eq]
  exact phaseCircleMeasure_angleAffineCosineSublevel_le_four_mul_of_quarter
    A B t ht hA hB hBA

/-- The source-interval phase estimate with an arbitrary real phase shift. -/
theorem sourceUniformInterval_shiftedAffineCosinePhaseSublevel_le_four_mul_of_quarter
    (δ A B t : ℝ) (ht : 0 ≤ t) (hA : (1 / 4 : ℝ) ≤ A)
    (hB : 0 ≤ B) (hBA : B ≤ A) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedAffineCosinePhaseSublevel δ A B t) ≤
      ENNReal.ofReal (4 * t) := by
  rw [sourceUniformInterval_shiftedAffineCosinePhaseSublevel_eq_phaseCircleMeasure]
  exact phaseCircleMeasure_shiftedAngleAffineCosineSublevel_le_four_mul_of_quarter
    (δ : Real.Angle) A B t ht hA hB hBA

end NLA.FR05

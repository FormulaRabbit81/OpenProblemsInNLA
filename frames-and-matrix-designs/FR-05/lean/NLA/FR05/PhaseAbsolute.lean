/-
The absolute affine-trigonometric phase branch in Lemma 3.6.

This temporary file first establishes the elementary inverse-cosine
square-root modulus which is the source of the `sqrt t` exponent at a
quadratic phase zero.
-/
import NLA.FR05.PhaseShift
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

local instance phasePeriodPositiveAbsolute : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- On `[-1, 1]`, the inverse-cosine gap has a square-root modulus.
This is sharp at either endpoint. -/
theorem arccos_gap_sq_le (x y : ℝ)
    (hy : -1 ≤ y) (hx : x ≤ 1) (hyx : y ≤ x) :
    (Real.arccos y - Real.arccos x) ^ 2 ≤
      (Real.pi ^ 2 / 2) * (x - y) := by
  let α : ℝ := Real.arccos x
  let β : ℝ := Real.arccos y
  have hα0 : 0 ≤ α := by
    exact Real.arccos_nonneg x
  have hβ0 : 0 ≤ β := by
    exact Real.arccos_nonneg y
  have hβpi : β ≤ Real.pi := by
    exact Real.arccos_le_pi y
  have hαβ : α ≤ β := by
    dsimp [α, β]
    exact Real.arccos_le_arccos hyx
  have hd0 : 0 ≤ β - α := sub_nonneg.mpr hαβ
  have hdpi : β - α ≤ Real.pi := by linarith
  have hhalf0 : 0 ≤ (β - α) / 2 := by linarith
  have hhalfpi : (β - α) / 2 ≤ Real.pi / 2 := by linarith
  have hjordan : (β - α) / Real.pi ≤ Real.sin ((β - α) / 2) := by
    have h := Real.mul_abs_le_abs_sin (show |(β - α) / 2| ≤ Real.pi / 2 by
      rw [abs_of_nonneg hhalf0]
      exact hhalfpi)
    rw [abs_of_nonneg hhalf0, abs_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 (by linarith : (β - α) / 2 ≤ Real.pi))] at h
    convert h using 1
    field_simp [Real.pi_ne_zero]
  have hsin_sq : ((β - α) / Real.pi) ^ 2 ≤
      Real.sin ((β - α) / 2) ^ 2 := by
    apply (sq_le_sq₀ (div_nonneg hd0 Real.pi_pos.le)
      (Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 (by linarith))).mpr
    exact hjordan
  have hsin_compare :
      Real.sin ((β - α) / 2) ≤ Real.sin ((α + β) / 2) := by
    have hsin : 0 ≤ Real.sin (α / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hcos : 0 ≤ Real.cos (β / 2) := by
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hident : Real.sin ((α + β) / 2) - Real.sin ((β - α) / 2) =
        2 * Real.sin (α / 2) * Real.cos (β / 2) := by
      rw [Real.sin_sub_sin]
      congr 3 <;> ring
    have hnonneg : 0 ≤ 2 * Real.sin (α / 2) * Real.cos (β / 2) := by
      positivity
    linarith [hident]
  have hcosdiff : Real.cos α - Real.cos β =
      2 * Real.sin ((α + β) / 2) * Real.sin ((β - α) / 2) := by
    rw [Real.cos_sub_cos]
    have hneg : (α - β) / 2 = -((β - α) / 2) := by ring
    rw [hneg, Real.sin_neg]
    ring
  have hcoslower : 2 * Real.sin ((β - α) / 2) ^ 2 ≤
      Real.cos α - Real.cos β := by
    rw [hcosdiff]
    have hsin0 : 0 ≤ Real.sin ((β - α) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hsin_compare) hsin0]
  have hcosxy : Real.cos α - Real.cos β = x - y := by
    dsimp [α, β]
    rw [Real.cos_arccos (by linarith) hx,
      Real.cos_arccos hy (by linarith)]
  rw [hcosxy] at hcoslower
  have hlower : 2 * ((β - α) / Real.pi) ^ 2 ≤ x - y := by
    exact le_trans (mul_le_mul_of_nonneg_left hsin_sq (by norm_num)) hcoslower
  have hmain : (β - α) ^ 2 ≤ (Real.pi ^ 2 / 2) * (x - y) := by
    calc
      (β - α) ^ 2 = (Real.pi ^ 2 / 2) *
          (2 * ((β - α) / Real.pi) ^ 2) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (Real.pi ^ 2 / 2) * (x - y) :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
  simpa only [α, β] using hmain

/-- A convenient square-root corollary of `arccos_gap_sq_le`. -/
theorem arccos_gap_le_pi_sqrt (x y h : ℝ)
    (hy : -1 ≤ y) (hx : x ≤ 1) (hyx : y ≤ x)
    (hh : 0 ≤ h) (hwidth : x - y ≤ 2 * h) :
    Real.arccos y - Real.arccos x ≤ Real.pi * Real.sqrt h := by
  have hgap := arccos_gap_sq_le x y hy hx hyx
  have hd0 : 0 ≤ Real.arccos y - Real.arccos x := by
    exact sub_nonneg.mpr (Real.arccos_le_arccos hyx)
  have hright0 : 0 ≤ Real.pi * Real.sqrt h := by positivity
  apply (sq_le_sq₀ hd0 hright0).mp
  calc
    (Real.arccos y - Real.arccos x) ^ 2 ≤
        (Real.pi ^ 2 / 2) * (x - y) := hgap
    _ ≤ (Real.pi ^ 2 / 2) * (2 * h) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = (Real.pi * Real.sqrt h) ^ 2 := by
      calc
        (Real.pi ^ 2 / 2) * (2 * h) = Real.pi ^ 2 * h := by ring
        _ = Real.pi ^ 2 * Real.sqrt h ^ 2 := by rw [Real.sq_sqrt hh]
        _ = (Real.pi * Real.sqrt h) ^ 2 := by ring

/-- The one-period sublevel set of a cosine at an arbitrary level. -/
def cosineBandPhaseSublevel (q h : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |Real.cos φ - q| ≤ h}

private def cosineBandClamp (x : ℝ) : ℝ := max (-1) (min 1 x)
private def cosineBandLower (q h : ℝ) : ℝ := cosineBandClamp (q - h)
private def cosineBandUpper (q h : ℝ) : ℝ := cosineBandClamp (q + h)

private theorem cosineBandClamp_monotone : Monotone cosineBandClamp := by
  intro x y hxy
  unfold cosineBandClamp
  exact max_le_max_left _ (min_le_min_left _ hxy)

private theorem cosineBandClamp_abs_sub_le (x y : ℝ) :
    |cosineBandClamp x - cosineBandClamp y| ≤ |x - y| := by
  have h := Set.abs_projIcc_sub_projIcc (a := (-1 : ℝ)) (b := 1)
    (c := x) (d := y) (by norm_num)
  simpa only [cosineBandClamp, Set.coe_projIcc] using h

private theorem neg_one_le_cosineBandClamp (x : ℝ) :
    -1 ≤ cosineBandClamp x := by
  unfold cosineBandClamp
  exact le_max_left _ _

private theorem cosineBandClamp_le_one (x : ℝ) :
    cosineBandClamp x ≤ 1 := by
  unfold cosineBandClamp
  exact max_le (by norm_num) (min_le_left _ _)

/-- A cosine band on one period has at most two monotone pieces. -/
theorem cosineBandPhaseSublevel_subset_twoIntervals (q h : ℝ) :
    cosineBandPhaseSublevel q h ⊆
      Icc (Real.arccos (cosineBandUpper q h))
          (Real.arccos (cosineBandLower q h)) ∪
        Icc (2 * Real.pi - Real.arccos (cosineBandLower q h))
          (2 * Real.pi - Real.arccos (cosineBandUpper q h)) := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ |Real.cos φ - q| ≤ h at hφ
  have hbandLower : q - h ≤ Real.cos φ := by
    have habs := (abs_le.mp hφ.2).1
    linarith
  have hbandUpper : Real.cos φ ≤ q + h := by
    have habs := (abs_le.mp hφ.2).2
    linarith
  have hlo : cosineBandLower q h ≤ Real.cos φ := by
    unfold cosineBandLower cosineBandClamp
    apply max_le (Real.neg_one_le_cos φ)
    exact (min_le_right _ _).trans hbandLower
  have hhi : Real.cos φ ≤ cosineBandUpper q h := by
    unfold cosineBandUpper cosineBandClamp
    exact (le_min (Real.cos_le_one φ) hbandUpper).trans (le_max_right _ _)
  rcases le_total φ Real.pi with hleft | hright
  · left
    have hα : Real.arccos (cosineBandUpper q h) ≤ φ := by
      calc
        Real.arccos (cosineBandUpper q h) ≤ Real.arccos (Real.cos φ) :=
          Real.arccos_le_arccos hhi
        _ = φ := Real.arccos_cos hφ.1.1 hleft
    have hβ : φ ≤ Real.arccos (cosineBandLower q h) := by
      calc
        φ = Real.arccos (Real.cos φ) := (Real.arccos_cos hφ.1.1 hleft).symm
        _ ≤ Real.arccos (cosineBandLower q h) :=
          Real.arccos_le_arccos hlo
    exact ⟨hα, hβ⟩
  · right
    let ψ : ℝ := 2 * Real.pi - φ
    have hψ0 : 0 ≤ ψ := by
      dsimp [ψ]
      linarith [hφ.1.2]
    have hψpi : ψ ≤ Real.pi := by
      dsimp [ψ]
      linarith
    have hcosψ : Real.cos ψ = Real.cos φ := by
      dsimp [ψ]
      exact Real.cos_two_pi_sub φ
    have hα : Real.arccos (cosineBandUpper q h) ≤ ψ := by
      calc
        Real.arccos (cosineBandUpper q h) ≤ Real.arccos (Real.cos ψ) := by
          rw [hcosψ]
          exact Real.arccos_le_arccos hhi
        _ = ψ := Real.arccos_cos hψ0 hψpi
    have hβ : ψ ≤ Real.arccos (cosineBandLower q h) := by
      calc
        ψ = Real.arccos (Real.cos ψ) := (Real.arccos_cos hψ0 hψpi).symm
        _ ≤ Real.arccos (cosineBandLower q h) := by
          rw [hcosψ]
          exact Real.arccos_le_arccos hlo
    dsimp [ψ] at hα hβ
    constructor <;> linarith

/-- Raw Lebesgue estimate for a cosine band.  The square-root dependence is
sharp when the level is tangent to the cosine at an endpoint. -/
theorem volume_cosineBandPhaseSublevel_le (q h : ℝ) (hh : 0 ≤ h) :
    volume (cosineBandPhaseSublevel q h) ≤
      ENNReal.ofReal (2 * Real.pi * Real.sqrt h) := by
  let lo : ℝ := cosineBandLower q h
  let hi : ℝ := cosineBandUpper q h
  have hshift : q - h ≤ q + h := by linarith
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi, cosineBandLower, cosineBandUpper]
    exact cosineBandClamp_monotone hshift
  have hloc : -1 ≤ lo := by
    dsimp [lo, cosineBandLower]
    exact neg_one_le_cosineBandClamp _
  have hhic : hi ≤ 1 := by
    dsimp [hi, cosineBandUpper]
    exact cosineBandClamp_le_one _
  have hclampWidth : hi - lo ≤ 2 * h := by
    have habs := cosineBandClamp_abs_sub_le (q + h) (q - h)
    have hright : |(q + h) - (q - h)| = 2 * h := by
      rw [abs_of_nonneg]
      · ring
      · linarith
    change cosineBandClamp (q + h) - cosineBandClamp (q - h) ≤ 2 * h
    calc
      cosineBandClamp (q + h) - cosineBandClamp (q - h) =
          |cosineBandClamp (q + h) - cosineBandClamp (q - h)| := by
        rw [abs_of_nonneg (sub_nonneg.mpr (cosineBandClamp_monotone hshift))]
      _ ≤ |(q + h) - (q - h)| := habs
      _ = 2 * h := hright
  have hgap : Real.arccos lo - Real.arccos hi ≤ Real.pi * Real.sqrt h :=
    arccos_gap_le_pi_sqrt hi lo h hloc hhic hlohi hh hclampWidth
  have hd0 : 0 ≤ Real.arccos lo - Real.arccos hi :=
    sub_nonneg.mpr (Real.arccos_le_arccos hlohi)
  let I₁ : Set ℝ := Icc (Real.arccos hi) (Real.arccos lo)
  let I₂ : Set ℝ := Icc (2 * Real.pi - Real.arccos lo)
    (2 * Real.pi - Real.arccos hi)
  have hsubset : cosineBandPhaseSublevel q h ⊆ I₁ ∪ I₂ := by
    simpa only [I₁, I₂, lo, hi] using
      cosineBandPhaseSublevel_subset_twoIntervals q h
  calc
    volume (cosineBandPhaseSublevel q h) ≤ volume (I₁ ∪ I₂) :=
      measure_mono hsubset
    _ ≤ volume I₁ + volume I₂ := measure_union_le I₁ I₂
    _ = ENNReal.ofReal (Real.arccos lo - Real.arccos hi) +
          ENNReal.ofReal (Real.arccos lo - Real.arccos hi) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      have hI₂ : 2 * Real.pi - Real.arccos hi -
          (2 * Real.pi - Real.arccos lo) =
          Real.arccos lo - Real.arccos hi := by ring
      rw [hI₂]
    _ = ENNReal.ofReal ((Real.arccos lo - Real.arccos hi) +
          (Real.arccos lo - Real.arccos hi)) := by
      rw [ENNReal.ofReal_add hd0 hd0]
    _ ≤ ENNReal.ofReal ((Real.pi * Real.sqrt h) +
          (Real.pi * Real.sqrt h)) := by
      apply ENNReal.ofReal_le_ofReal
      linarith
    _ = ENNReal.ofReal (2 * Real.pi * Real.sqrt h) := by
      congr 1
      ring

theorem measurableSet_cosineBandPhaseSublevel (q h : ℝ) :
    MeasurableSet (cosineBandPhaseSublevel q h) := by
  unfold cosineBandPhaseSublevel
  apply measurableSet_Icc.inter
  exact measurableSet_le
    ((Real.continuous_cos.measurable.sub measurable_const).abs)
    measurable_const

/-- The source's uniform phase law assigns a cosine band probability at most
the square root of its width. -/
theorem sourceUniformInterval_cosineBandPhaseSublevel_le_sqrt
    (q h : ℝ) (hh : 0 ≤ h) :
    sourceUniformInterval 0 (2 * Real.pi) (cosineBandPhaseSublevel q h) ≤
      ENNReal.ofReal (Real.sqrt h) := by
  have hsub : cosineBandPhaseSublevel q h ⊆ Icc 0 (2 * Real.pi) := by
    intro φ hφ
    exact hφ.1
  have hvol := volume_cosineBandPhaseSublevel_le q h hh
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpi).ne'
  unfold sourceUniformInterval ProbabilityTheory.cond
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc,
    Measure.restrict_apply (measurableSet_cosineBandPhaseSublevel q h),
    Set.inter_eq_left.mpr hsub]
  simp only [sub_zero]
  calc
    (ENNReal.ofReal (2 * Real.pi))⁻¹ * volume (cosineBandPhaseSublevel q h) ≤
        (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ENNReal.ofReal (2 * Real.pi * Real.sqrt h) :=
      mul_le_mul_of_nonneg_left hvol bot_le
    _ = ENNReal.ofReal (Real.sqrt h) := by
      rw [ENNReal.ofReal_mul hpi.le, ← mul_assoc,
        ENNReal.inv_mul_cancel hpi0 ENNReal.ofReal_ne_top, one_mul]

/-- The cosine band written on the additive phase circle. -/
def angleCosineBandPhaseSublevel (q h : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | |Real.Angle.cos θ - q| ≤ h}

/-- The same band after a phase translation. -/
def shiftedAngleCosineBandPhaseSublevel
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | |Real.Angle.cos (δ + θ) - q| ≤ h}

/-- The shifted band on the source interval. -/
def shiftedCosineBandPhaseSublevel (δ q h : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |Real.cos (δ + φ) - q| ≤ h}

theorem measurableSet_angleCosineBandPhaseSublevel (q h : ℝ) :
    MeasurableSet (angleCosineBandPhaseSublevel q h) := by
  unfold angleCosineBandPhaseSublevel
  have hcos : Measurable
      (fun θ : AddCircle (2 * Real.pi) => Real.Angle.cos θ) := by
    apply Continuous.measurable
    exact Real.Angle.continuous_cos
  exact measurableSet_le (hcos.sub measurable_const).abs measurable_const

theorem shiftedAngleCosineBandPhaseSublevel_eq_preimage
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    shiftedAngleCosineBandPhaseSublevel δ q h =
      (fun θ : AddCircle (2 * Real.pi) => δ + θ) ⁻¹'
        angleCosineBandPhaseSublevel q h := by
  rfl

theorem measurableSet_shiftedAngleCosineBandPhaseSublevel
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    MeasurableSet (shiftedAngleCosineBandPhaseSublevel δ q h) := by
  rw [shiftedAngleCosineBandPhaseSublevel_eq_preimage]
  exact (measurableSet_angleCosineBandPhaseSublevel q h).preimage
    (measurePreserving_add_left volume δ).measurable

theorem volume_shiftedAngleCosineBandPhaseSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    volume (shiftedAngleCosineBandPhaseSublevel δ q h) =
      volume (angleCosineBandPhaseSublevel q h) := by
  rw [shiftedAngleCosineBandPhaseSublevel_eq_preimage]
  exact (measurePreserving_add_left volume δ).measure_preimage
    (measurableSet_angleCosineBandPhaseSublevel q h).nullMeasurableSet

theorem measurableSet_shiftedCosineBandPhaseSublevel (δ q h : ℝ) :
    MeasurableSet (shiftedCosineBandPhaseSublevel δ q h) := by
  unfold shiftedCosineBandPhaseSublevel
  apply measurableSet_Icc.inter
  have hcos : Measurable (fun φ : ℝ => Real.cos (δ + φ)) := by fun_prop
  exact measurableSet_le (hcos.sub measurable_const).abs measurable_const

theorem volume_angleCosineBandPhaseSublevel_eq_volume_cosineBandPhaseSublevel
    (q h : ℝ) :
    volume (angleCosineBandPhaseSublevel q h) =
      volume (cosineBandPhaseSublevel q h) := by
  let coeAngle : ℝ → AddCircle (2 * Real.pi) := fun x => (x : Real.Angle)
  have hpremeas : MeasurableSet
      (coeAngle ⁻¹' angleCosineBandPhaseSublevel q h) :=
    (measurableSet_angleCosineBandPhaseSublevel q h).preimage
      AddCircle.measurable_mk'
  have hmeasure := (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measure_preimage
    (measurableSet_angleCosineBandPhaseSublevel q h).nullMeasurableSet
  have hrestrict : volume.restrict (Ioc 0 (2 * Real.pi)) =
      volume.restrict (Icc 0 (2 * Real.pi)) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  calc
    volume (angleCosineBandPhaseSublevel q h) =
        (volume.restrict (Ioc 0 (2 * Real.pi)))
          (coeAngle ⁻¹' angleCosineBandPhaseSublevel q h) := by
      simpa [coeAngle, Real.Angle.coe] using hmeasure.symm
    _ = (volume.restrict (Icc 0 (2 * Real.pi)))
          (coeAngle ⁻¹' angleCosineBandPhaseSublevel q h) := by rw [hrestrict]
    _ = volume (cosineBandPhaseSublevel q h) := by
      rw [Measure.restrict_apply hpremeas]
      congr 1
      ext φ
      simp only [Set.mem_inter_iff, coeAngle,
        angleCosineBandPhaseSublevel, cosineBandPhaseSublevel]
      constructor <;> intro hφ
      · exact ⟨hφ.2, hφ.1⟩
      · exact ⟨hφ.2, hφ.1⟩

theorem sourceUniformInterval_cosineBandPhaseSublevel_eq_phaseCircleMeasure
    (q h : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi) (cosineBandPhaseSublevel q h) =
      phaseCircleMeasure (angleCosineBandPhaseSublevel q h) := by
  have hsub : cosineBandPhaseSublevel q h ⊆ Icc 0 (2 * Real.pi) := by
    intro φ hφ
    exact hφ.1
  unfold sourceUniformInterval ProbabilityTheory.cond phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc,
    Measure.restrict_apply (measurableSet_cosineBandPhaseSublevel q h),
    Set.inter_eq_left.mpr hsub, Measure.smul_apply, smul_eq_mul,
    volume_angleCosineBandPhaseSublevel_eq_volume_cosineBandPhaseSublevel]
  congr 1
  ring_nf

theorem sourceUniformInterval_shiftedCosineBandPhaseSublevel_eq_phaseCircleMeasure
    (δ q h : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedCosineBandPhaseSublevel δ q h) =
      phaseCircleMeasure
        (shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) := by
  have hsub : shiftedCosineBandPhaseSublevel δ q h ⊆ Icc 0 (2 * Real.pi) := by
    intro φ hφ
    exact hφ.1
  let coeAngle : ℝ → AddCircle (2 * Real.pi) := fun x => (x : Real.Angle)
  have hpremeas : MeasurableSet
      (coeAngle ⁻¹' shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) :=
    (measurableSet_shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h).preimage
      AddCircle.measurable_mk'
  have hmeasure := (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measure_preimage
    (measurableSet_shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h).nullMeasurableSet
  have hrestrict : volume.restrict (Ioc 0 (2 * Real.pi)) =
      volume.restrict (Icc 0 (2 * Real.pi)) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  unfold sourceUniformInterval ProbabilityTheory.cond phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc,
    Measure.restrict_apply (measurableSet_shiftedCosineBandPhaseSublevel δ q h),
    Set.inter_eq_left.mpr hsub, Measure.smul_apply, smul_eq_mul]
  have hvolume : volume
      (shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) =
      volume (shiftedCosineBandPhaseSublevel δ q h) := by
    calc
      volume (shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) =
          (volume.restrict (Ioc 0 (2 * Real.pi)))
            (coeAngle ⁻¹' shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) := by
        simpa [coeAngle, Real.Angle.coe] using hmeasure.symm
      _ = (volume.restrict (Icc 0 (2 * Real.pi)))
            (coeAngle ⁻¹' shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) := by
        rw [hrestrict]
      _ = volume (shiftedCosineBandPhaseSublevel δ q h) := by
        rw [Measure.restrict_apply hpremeas]
        congr 1
        ext φ
        simp only [Set.mem_inter_iff, coeAngle,
          shiftedAngleCosineBandPhaseSublevel, shiftedCosineBandPhaseSublevel]
        constructor <;> intro hφ
        · exact ⟨hφ.2, hφ.1⟩
        · exact ⟨hφ.2, hφ.1⟩
  rw [hvolume]
  congr 1
  ring_nf

theorem phaseCircleMeasure_shiftedAngleCosineBandPhaseSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    phaseCircleMeasure (shiftedAngleCosineBandPhaseSublevel δ q h) =
      phaseCircleMeasure (angleCosineBandPhaseSublevel q h) := by
  unfold phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul,
    volume_shiftedAngleCosineBandPhaseSublevel_eq]

/-- Translation invariance extends the cosine-band estimate to any phase
offset. -/
theorem sourceUniformInterval_shiftedCosineBandPhaseSublevel_le_sqrt
    (δ q h : ℝ) (hh : 0 ≤ h) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedCosineBandPhaseSublevel δ q h) ≤ ENNReal.ofReal (Real.sqrt h) := by
  rw [sourceUniformInterval_shiftedCosineBandPhaseSublevel_eq_phaseCircleMeasure]
  change phaseCircleMeasure
      (shiftedAngleCosineBandPhaseSublevel (δ : AddCircle (2 * Real.pi)) q h) ≤ _
  rw [phaseCircleMeasure_shiftedAngleCosineBandPhaseSublevel_eq,
    ← sourceUniformInterval_cosineBandPhaseSublevel_eq_phaseCircleMeasure]
  exact sourceUniformInterval_cosineBandPhaseSublevel_le_sqrt q h hh

/-- The deterministic trigonometric term in the second branch of Lemma 3.6. -/
def affineTrig (a b c φ : ℝ) : ℝ :=
  a + b * Real.cos φ + c * Real.sin φ

private def affineTrigPhaseCoefficient (b c : ℝ) : ℂ :=
  (b : ℂ) - (c : ℂ) * Complex.I

def affineTrigAmplitude (b c : ℝ) : ℝ := Real.sqrt (b ^ 2 + c ^ 2)

def affineTrigPhase (b c : ℝ) : ℝ :=
  Complex.arg (affineTrigPhaseCoefficient b c)

private theorem complex_exp_phase_re (z : ℂ) (φ : ℝ) :
    (Complex.exp ((φ : ℂ) * Complex.I) * z).re =
      ‖z‖ * Real.cos (Complex.arg z + φ) := by
  have hpolar := Complex.norm_mul_exp_arg_mul_I z
  have hproduct :
      Complex.exp ((φ : ℂ) * Complex.I) * z =
        ((‖z‖ : ℝ) : ℂ) *
          Complex.exp (((Complex.arg z + φ : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.exp ((φ : ℂ) * Complex.I) * z =
          Complex.exp ((φ : ℂ) * Complex.I) *
            (((‖z‖ : ℝ) : ℂ) *
              Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by
        rw [hpolar]
      _ = ((‖z‖ : ℝ) : ℂ) *
            Complex.exp ((Complex.arg z : ℂ) * Complex.I) *
              Complex.exp ((φ : ℂ) * Complex.I) := by ring
      _ = ((‖z‖ : ℝ) : ℂ) *
            Complex.exp ((Complex.arg z : ℂ) * Complex.I +
              (φ : ℂ) * Complex.I) := by
        rw [Complex.exp_add]
        ring
      _ = ((‖z‖ : ℝ) : ℂ) *
            Complex.exp (((Complex.arg z + φ : ℝ) : ℂ) * Complex.I) := by
        congr 2
        push_cast
        ring
  rw [hproduct, Complex.exp_ofReal_mul_I (Complex.arg z + φ)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]

private theorem affineTrigPhaseCoefficient_re (b c φ : ℝ) :
    (Complex.exp ((φ : ℂ) * Complex.I) * affineTrigPhaseCoefficient b c).re =
      b * Real.cos φ + c * Real.sin φ := by
  unfold affineTrigPhaseCoefficient
  rw [Complex.exp_ofReal_mul_I]
  simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

private theorem norm_affineTrigPhaseCoefficient (b c : ℝ) :
    ‖affineTrigPhaseCoefficient b c‖ = affineTrigAmplitude b c := by
  unfold affineTrigPhaseCoefficient affineTrigAmplitude
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    Complex.sub_im, Complex.mul_im, mul_one, sub_zero]
  ring_nf

/-- Polar normalization of the full affine trigonometric polynomial. -/
theorem affineTrig_cosine_normalForm (a b c φ : ℝ) :
    affineTrig a b c φ =
      a + affineTrigAmplitude b c * Real.cos (affineTrigPhase b c + φ) := by
  unfold affineTrig affineTrigPhase
  calc
    a + b * Real.cos φ + c * Real.sin φ =
        a + (b * Real.cos φ + c * Real.sin φ) := by ring
    _ = a +
        (Complex.exp ((φ : ℂ) * Complex.I) * affineTrigPhaseCoefficient b c).re := by
      rw [affineTrigPhaseCoefficient_re]
    _ = a + affineTrigAmplitude b c *
        Real.cos (Complex.arg (affineTrigPhaseCoefficient b c) + φ) := by
      rw [complex_exp_phase_re, norm_affineTrigPhaseCoefficient]

theorem affineTrigAmplitude_sq (b c : ℝ) :
    affineTrigAmplitude b c ^ 2 = b ^ 2 + c ^ 2 := by
  unfold affineTrigAmplitude
  exact Real.sq_sqrt (by positivity)

theorem affineTrigAmplitude_nonneg (b c : ℝ) :
    0 ≤ affineTrigAmplitude b c := Real.sqrt_nonneg _

/-- The absolute affine-trigonometric sublevel event on one source phase
period. -/
def affineTrigPhaseSublevel (a b c t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |affineTrig a b c φ| ≤ t}

theorem measurableSet_affineTrigPhaseSublevel (a b c t : ℝ) :
    MeasurableSet (affineTrigPhaseSublevel a b c t) := by
  unfold affineTrigPhaseSublevel affineTrig
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (((measurable_const.add (measurable_const.mul Real.continuous_cos.measurable)).add
      (measurable_const.mul Real.continuous_sin.measurable)).abs)
    measurable_const

theorem affineTrigPhaseSublevel_subset_shiftedCosineBand
    (a b c t : ℝ) (hR : 0 < affineTrigAmplitude b c) :
    affineTrigPhaseSublevel a b c t ⊆
      shiftedCosineBandPhaseSublevel (affineTrigPhase b c)
        (-a / affineTrigAmplitude b c) (t / affineTrigAmplitude b c) := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ |affineTrig a b c φ| ≤ t at hφ
  constructor
  · exact hφ.1
  rw [affineTrig_cosine_normalForm] at hφ
  have hfactor : a + affineTrigAmplitude b c *
      Real.cos (affineTrigPhase b c + φ) =
      affineTrigAmplitude b c *
        (Real.cos (affineTrigPhase b c + φ) -
          (-a / affineTrigAmplitude b c)) := by
    field_simp [hR.ne']
    ring
  rw [hfactor, abs_mul, abs_of_pos hR] at hφ
  apply (le_div_iff₀ hR).mpr
  simpa only [mul_comm] using hφ.2

/-- The phase-band result instantiated for a nonzero affine trigonometric
polynomial. -/
theorem sourceUniformInterval_affineTrigPhaseSublevel_le_sqrt_div
    (a b c t : ℝ) (ht : 0 ≤ t) (hR : 0 < affineTrigAmplitude b c) :
    sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
      ENNReal.ofReal (Real.sqrt (t / affineTrigAmplitude b c)) := by
  calc
    sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
        sourceUniformInterval 0 (2 * Real.pi)
          (shiftedCosineBandPhaseSublevel (affineTrigPhase b c)
            (-a / affineTrigAmplitude b c) (t / affineTrigAmplitude b c)) :=
      measure_mono (affineTrigPhaseSublevel_subset_shiftedCosineBand a b c t hR)
    _ ≤ ENNReal.ofReal (Real.sqrt (t / affineTrigAmplitude b c)) :=
      sourceUniformInterval_shiftedCosineBandPhaseSublevel_le_sqrt _ _ _
        (div_nonneg ht hR.le)

theorem abs_affineTrig_sub_const_le_amplitude (a b c φ : ℝ) :
    |affineTrig a b c φ - a| ≤ affineTrigAmplitude b c := by
  rw [affineTrig_cosine_normalForm]
  have hR : 0 ≤ affineTrigAmplitude b c := affineTrigAmplitude_nonneg b c
  calc
    |a + affineTrigAmplitude b c * Real.cos (affineTrigPhase b c + φ) - a| =
        |affineTrigAmplitude b c * Real.cos (affineTrigPhase b c + φ)| := by
      congr 1
      ring
    _ = affineTrigAmplitude b c * |Real.cos (affineTrigPhase b c + φ)| := by
      rw [abs_mul, abs_of_nonneg hR]
    _ ≤ affineTrigAmplitude b c * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hR
    _ = affineTrigAmplitude b c := by ring

/-- In the small-amplitude alternative of the source proof, coefficient
energy forces the affine trigonometric polynomial away from zero. -/
theorem affineTrig_abs_ge_half_of_small_amplitude
    (a b c φ : ℝ)
    (hcoeff : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2)
    (hamp : affineTrigAmplitude b c ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ |affineTrig a b c φ| := by
  have hR0 : 0 ≤ affineTrigAmplitude b c := affineTrigAmplitude_nonneg b c
  have hRsq : affineTrigAmplitude b c ^ 2 ≤ (1 / 16 : ℝ) := by
    nlinarith
  have htailSq : b ^ 2 + c ^ 2 ≤ (1 / 16 : ℝ) := by
    rw [← affineTrigAmplitude_sq]
    exact hRsq
  have haSq : (3 / 4 : ℝ) ^ 2 ≤ a ^ 2 := by
    nlinarith
  have haAbs : (3 / 4 : ℝ) ≤ |a| := by
    apply (sq_le_sq₀ (by norm_num) (abs_nonneg a)).mp
    simpa only [sq_abs] using haSq
  have hdev : |affineTrig a b c φ - a| ≤ affineTrigAmplitude b c :=
    abs_affineTrig_sub_const_le_amplitude a b c φ
  have htri : |a| ≤ |affineTrig a b c φ| +
      |affineTrig a b c φ - a| := by
    calc
      |a| = |affineTrig a b c φ + (a - affineTrig a b c φ)| := by
        congr 1
        ring
      _ ≤ |affineTrig a b c φ| + |a - affineTrig a b c φ| := abs_add_le _ _
      _ = |affineTrig a b c φ| + |affineTrig a b c φ - a| := by
        rw [abs_sub_comm]
  nlinarith

theorem affineTrigPhaseSublevel_subset_empty_of_small_amplitude
    (a b c t : ℝ)
    (hcoeff : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2)
    (hamp : affineTrigAmplitude b c ≤ 1 / 4)
    (ht : t < 1 / 2) :
    affineTrigPhaseSublevel a b c t ⊆ ∅ := by
  intro φ hφ
  have hlarge : (1 / 2 : ℝ) ≤ |affineTrig a b c φ| :=
    affineTrig_abs_ge_half_of_small_amplitude a b c φ hcoeff hamp
  exact (not_le_of_gt ht) (hlarge.trans hφ.2)

/-- The source's second (non-tail) branch: an absolute affine
trigonometric polynomial whose coefficient energy is bounded below has
one-period small-ball probability `O(sqrt t)`.  The exponent is sharp at a
quadratic phase zero. -/
theorem sourceUniformInterval_affineTrigPhaseSublevel_le_two_sqrt
    (a b c t : ℝ) (ht : 0 ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2) :
    sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
      ENNReal.ofReal (2 * Real.sqrt t) := by
  rcases le_total (affineTrigAmplitude b c) (1 / 4 : ℝ) with hamp | hamp
  · rcases lt_or_ge t (1 / 2 : ℝ) with htSmall | htLarge
    · calc
        sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
            sourceUniformInterval 0 (2 * Real.pi) ∅ :=
          measure_mono (affineTrigPhaseSublevel_subset_empty_of_small_amplitude
            a b c t hcoeff hamp htSmall)
        _ = 0 := measure_empty
        _ ≤ ENNReal.ofReal (2 * Real.sqrt t) := bot_le
    · have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt t := by
        apply (Real.le_sqrt (by norm_num) ht).mpr
        nlinarith
      calc
        sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
            sourceUniformInterval 0 (2 * Real.pi) (Icc 0 (2 * Real.pi)) := by
          apply measure_mono
          intro φ hφ
          exact hφ.1
        _ = 1 := sourceUniformInterval_apply_self (by positivity)
        _ = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal (2 * Real.sqrt t) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  · have hRpos : 0 < affineTrigAmplitude b c :=
      lt_of_lt_of_le (by norm_num) hamp
    have hquot : t / affineTrigAmplitude b c ≤ 4 * t := by
      calc
        t / affineTrigAmplitude b c ≤ t / (1 / 4 : ℝ) :=
          div_le_div_of_nonneg_left ht (by norm_num) hamp
        _ = 4 * t := by ring
    have hsqrt : Real.sqrt (t / affineTrigAmplitude b c) ≤ 2 * Real.sqrt t := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      calc
        Real.sqrt (t / affineTrigAmplitude b c) ^ 2 =
            t / affineTrigAmplitude b c :=
          Real.sq_sqrt (div_nonneg ht hRpos.le)
        _ ≤ 4 * t := hquot
        _ = (2 * Real.sqrt t) ^ 2 := by
          calc
            4 * t = 4 * Real.sqrt t ^ 2 := by rw [Real.sq_sqrt ht]
            _ = (2 * Real.sqrt t) ^ 2 := by ring
    exact (sourceUniformInterval_affineTrigPhaseSublevel_le_sqrt_div
      a b c t ht hRpos).trans (ENNReal.ofReal_le_ofReal hsqrt)

/-- The scalar phase term in equation (3.21), written with the source's
normalization.  Its constant coefficient is half of the first real
coordinate. -/
def sourceScalarPhase (σ β γ φ : ℝ) : ℝ :=
  σ / 2 + β * Real.cos φ - γ * Real.sin φ

/-- The source-normalized scalar phase sublevel event on one period. -/
def sourceScalarPhaseSublevel (σ β γ t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |sourceScalarPhase σ β γ φ| ≤ t}

theorem measurableSet_sourceScalarPhaseSublevel (σ β γ t : ℝ) :
    MeasurableSet (sourceScalarPhaseSublevel σ β γ t) := by
  unfold sourceScalarPhaseSublevel sourceScalarPhase
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (((measurable_const.add (measurable_const.mul Real.continuous_cos.measurable)).sub
      (measurable_const.mul Real.continuous_sin.measurable)).abs)
    measurable_const

theorem affineTrig_scaled_eq_two_mul_sourceScalarPhase (σ β γ φ : ℝ) :
    affineTrig σ (2 * β) (-2 * γ) φ =
      2 * sourceScalarPhase σ β γ φ := by
  unfold affineTrig sourceScalarPhase
  ring

/-- To invoke the coefficient-energy phase theorem on the source scalar
term, one must first multiply it by two.  This avoids incorrectly treating
the source coefficient `σ / 2` as if it carried full `σ²` energy. -/
theorem sourceScalarPhaseSublevel_eq_affineTrigPhaseSublevel
    (σ β γ t : ℝ) :
    sourceScalarPhaseSublevel σ β γ t =
      affineTrigPhaseSublevel σ (2 * β) (-2 * γ) (2 * t) := by
  ext φ
  unfold sourceScalarPhaseSublevel affineTrigPhaseSublevel
  simp only [Set.mem_ofPred_eq]
  rw [affineTrig_scaled_eq_two_mul_sourceScalarPhase]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  constructor <;> intro h
  · exact ⟨h.1, by nlinarith [h.2]⟩
  · exact ⟨h.1, by nlinarith [h.2]⟩

/-- The source's non-tail scalar branch, in precisely the normalization of
equation (3.21).  Multiplying by two transfers the stated coefficient-energy
assumption to the affine-trigonometric estimate. -/
theorem sourceUniformInterval_sourceScalarPhaseSublevel_le_two_sqrt_two_mul
    (σ β γ t : ℝ) (ht : 0 ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ σ ^ 2 + β ^ 2 + γ ^ 2) :
    sourceUniformInterval 0 (2 * Real.pi)
        (sourceScalarPhaseSublevel σ β γ t) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) := by
  rw [sourceScalarPhaseSublevel_eq_affineTrigPhaseSublevel]
  apply sourceUniformInterval_affineTrigPhaseSublevel_le_two_sqrt
  · linarith
  · nlinarith [sq_nonneg β, sq_nonneg γ]

end NLA.FR05

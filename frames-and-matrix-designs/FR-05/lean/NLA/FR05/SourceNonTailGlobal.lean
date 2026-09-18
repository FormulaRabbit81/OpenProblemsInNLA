/-
Outer source-law assembly for the scalar-dominated branch of Lemma 3.6.

The conditional non-tail calculation is uniform in the radial coordinate,
imbalance, and first phase. This file reassociates the exact five-factor
source law and integrates those independent factors without replacing the
source distribution by a surrogate.
-/
import NLA.FR05.SourceNonTailConditional
import NLA.FR05.SourceRowSmallBallEvent
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The scalar-dominated source-row event in the right-associated coordinate
order `S, xi, alpha, (phi, w)`. The first-phase support is included so that
off-support sections are empty. -/
def sourceNonTailSmallBallEventRight {n : ℕ}
    (p q : Signal n) (sigma beta gamma u : ℝ) :
    Set (ℝ × (ℝ × (ℝ × (ℝ × Signal n)))) :=
  {x | x.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
    x.2.2.2 ∈ sourceNonTailConditionalSmallBallEvent p q sigma beta gamma
      x.1 x.2.2.1 u}

theorem measurableSet_sourceNonTailSmallBallEventRight {n : ℕ}
    (p q : Signal n) (sigma beta gamma u : ℝ) :
    MeasurableSet (sourceNonTailSmallBallEventRight p q sigma beta gamma u) := by
  unfold sourceNonTailSmallBallEventRight sourceNonTailConditionalSmallBallEvent
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc (by fun_prop)
  · apply MeasurableSet.inter
    · exact MeasurableSet.preimage measurableSet_Icc (by fun_prop)
    · change MeasurableSet
        ((fun x : ℝ × (ℝ × (ℝ × (ℝ × Signal n))) ↦
          |sourceJacobianPhaseCenter sigma beta gamma x.2.2.1 x.2.2.2.1 +
            Real.sqrt (2 / x.1) *
              (star (Complex.exp ((-x.2.2.1 : ℂ) * Complex.I) • x.2.2.2.2) ⬝ᵥ
                (p + Complex.exp (((x.2.2.2.1 - x.2.2.1 : ℝ) : ℂ) * Complex.I) • q)).re|) ⁻¹'
          Iic u)
      apply MeasurableSet.preimage measurableSet_Iic
      unfold sourceJacobianPhaseCenter
      fun_prop

/-- Integrate the scalar-dominated conditional estimate through the three
outer independent source factors. -/
theorem sourceCoordinateLawRight_sourceNonTailSmallBall_le
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLawRight eta delta epsilon n
        (sourceNonTailSmallBallEventRight p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let muS := sourceRadialLaw eta delta
  let muxi := sourceUniformInterval (-epsilon) epsilon
  let mualpha := sourceUniformInterval 0 (2 * Real.pi)
  let muphi := sourceUniformInterval 0 (2 * Real.pi)
  let nu := standardComplexGaussianTail n
  letI : IsProbabilityMeasure muS := by
    dsimp [muS]
    exact isProbabilityMeasure_sourceRadialLaw heta0 heta1
  letI : IsProbabilityMeasure muxi := by
    dsimp [muxi]
    exact isProbabilityMeasure_sourceUniformInterval (by linarith)
  letI : IsProbabilityMeasure mualpha := by
    dsimp [mualpha]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  letI : IsProbabilityMeasure muphi := by
    dsimp [muphi]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    exact isProbabilityMeasure_standardComplexGaussianTail n
  change (muS.prod (muxi.prod (mualpha.prod (muphi.prod nu))))
      (sourceNonTailSmallBallEventRight p q sigma beta gamma u) ≤ _
  apply prod_measure_le_of_sections_le muS (muxi.prod (mualpha.prod (muphi.prod nu)))
    (measurableSet_sourceNonTailSmallBallEventRight p q sigma beta gamma u) _
  intro S
  have hSsection : MeasurableSet
      {x : ℝ × (ℝ × (ℝ × Signal n)) |
        (S, x) ∈ sourceNonTailSmallBallEventRight p q sigma beta gamma u} :=
    measurable_prodMk_left
      (measurableSet_sourceNonTailSmallBallEventRight p q sigma beta gamma u)
  apply prod_measure_le_of_sections_le muxi (mualpha.prod (muphi.prod nu)) hSsection _
  intro xi
  have hxisection : MeasurableSet
      {x : ℝ × (ℝ × Signal n) |
        (xi, x) ∈ {y : ℝ × (ℝ × (ℝ × Signal n)) |
          (S, y) ∈ sourceNonTailSmallBallEventRight p q sigma beta gamma u}} :=
    measurable_prodMk_left hSsection
  apply prod_measure_le_of_sections_le mualpha (muphi.prod nu) hxisection _
  intro alpha
  by_cases halpha : alpha ∈ Icc 0 (2 * Real.pi)
  · change (muphi.prod nu)
      {z | alpha ∈ Icc 0 (2 * Real.pi) ∧
        z ∈ sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u} ≤ _
    simp only [halpha, true_and]
    exact sourceUniformInterval_prod_sourceNonTailConditionalSmallBall_le
      p q sigma beta gamma S alpha u t ht hscale hcoeff
  · have hempty :
      {z : ℝ × Signal n |
        (alpha, z) ∈ {x : ℝ × (ℝ × Signal n) |
          (xi, x) ∈ {y : ℝ × (ℝ × (ℝ × Signal n)) |
            (S, y) ∈ sourceNonTailSmallBallEventRight p q sigma beta gamma u}}} = ∅ := by
        ext z
        change (alpha ∈ Icc 0 (2 * Real.pi) ∧
          z ∈ sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u) ↔
          z ∈ (∅ : Set (ℝ × Signal n))
        simp [halpha]
    rw [hempty, measure_empty]
    exact bot_le

/-- Pull the right-associated scalar-branch event back to the repository's
native source-coordinate order. -/
def sourceNonTailSmallBallEventOnCoordinates {n : ℕ}
    (p q : Signal n) (sigma beta gamma u : ℝ) : Set (SourcePlantedCoordinates n) :=
  (sourceCoordinateReassoc n) ⁻¹'
    sourceNonTailSmallBallEventRight p q sigma beta gamma u

/-- On source support, the reassociated scalar-branch event is the literal
source-row small-ball event with its two phase support clauses displayed. -/
theorem mem_sourceNonTailSmallBallEventOnCoordinates_iff
    {n : ℕ} (x : SourcePlantedCoordinates n) (hS : 0 < x.1.1)
    (hxi : |x.1.2.1| ≤ 1) (p q : Signal n) (sigma beta gamma u : ℝ) :
    x ∈ sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u ↔
      x.1.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
        x.1.2.2.2 ∈ Icc 0 (2 * Real.pi) ∧
        |sourceRowJacobianForm (sourceCoordinatesToPlantedRow x hS hxi)
          sigma beta gamma p q| ≤ u := by
  rfl

/-- Under full source support, the literal row event lies in the exact
scalar-branch coordinate event. -/
theorem ae_sourceRowJacobianSmallBall_subset_nonTail
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hepsilon1 : epsilon ≤ 1) :
    sourceRowJacobianSmallBallEvent p q sigma beta gamma u
      ≤ᵐ[sourceCoordinateLaw eta delta epsilon n]
        sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u := by
  filter_upwards [ae_sourceCoordinateLaw_fullSupport n heta0 heta1 hepsilon hdelta hepsilon1]
    with x hx
  intro hsmall
  change x ∈ sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u
  rw [mem_sourceNonTailSmallBallEventOnCoordinates_iff
    x hx.1 hx.2.1 p q sigma beta gamma u]
  refine ⟨hx.2.2.1, hx.2.2.2, ?_⟩
  have hsupp : 0 < x.1.1 ∧ |x.1.2.1| ≤ 1 := ⟨hx.1, hx.2.1⟩
  have hdefault : sourceCoordinatesToPlantedRowOrDefault x =
      sourceCoordinatesToPlantedRow x hx.1 hx.2.1 := by
    simp [sourceCoordinatesToPlantedRowOrDefault, hsupp]
  change |sourceRowJacobianForm (sourceCoordinatesToPlantedRowOrDefault x)
    sigma beta gamma p q| ≤ u at hsmall
  rw [hdefault] at hsmall
  exact hsmall

/-- The non-tail scalar branch under the exact source-coordinate law. -/
theorem sourceCoordinateLaw_nonTailSmallBall_le
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLaw eta delta epsilon n
        (sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  have hmeas := measurableSet_sourceNonTailSmallBallEventRight p q sigma beta gamma u
  calc
    sourceCoordinateLaw eta delta epsilon n
        (sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u) =
        Measure.map (sourceCoordinateReassoc n) (sourceCoordinateLaw eta delta epsilon n)
          (sourceNonTailSmallBallEventRight p q sigma beta gamma u) := by
      unfold sourceNonTailSmallBallEventOnCoordinates
      rw [Measure.map_apply (sourceCoordinateReassoc n).measurable hmeas]
    _ = sourceCoordinateLawRight eta delta epsilon n
        (sourceNonTailSmallBallEventRight p q sigma beta gamma u) := by
      rw [sourceCoordinateLaw_map_reassoc eta delta epsilon n heta0 heta1 hepsilon]
    _ ≤ _ := sourceCoordinateLawRight_sourceNonTailSmallBall_le
      eta delta epsilon p q sigma beta gamma u t heta0 heta1 hepsilon ht hscale hcoeff

/-- Literal source-row version of the scalar-dominated small-ball estimate. -/
theorem sourceCoordinateLaw_sourceRowJacobianSmallBall_nonTail_le
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hepsilon1 : epsilon ≤ 1)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLaw eta delta epsilon n
        (sourceRowJacobianSmallBallEvent p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  calc
    sourceCoordinateLaw eta delta epsilon n
        (sourceRowJacobianSmallBallEvent p q sigma beta gamma u) ≤
        sourceCoordinateLaw eta delta epsilon n
          (sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u) :=
      measure_mono_ae (ae_sourceRowJacobianSmallBall_subset_nonTail
        eta delta epsilon p q sigma beta gamma u
        heta0 heta1 hepsilon hdelta hepsilon1)
    _ ≤ _ := sourceCoordinateLaw_nonTailSmallBall_le
      eta delta epsilon p q sigma beta gamma u t
      heta0 heta1 hepsilon ht hscale hcoeff

/-- Manuscript-parameter specialization of the literal scalar-dominated
source-row estimate. -/
theorem sourceCoordinateLaw_sourceM_sourceRowJacobianSmallBall_nonTail_le
    {M n : ℕ} (hM : 1 ≤ M) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
        (sourceRowJacobianSmallBallEvent p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  exact sourceCoordinateLaw_sourceRowJacobianSmallBall_nonTail_le
    sourceEta (sourceDelta M) (sourceEpsilon M) p q sigma beta gamma u t
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M hM)
    (sourceDelta_pos M hM) (sourceEpsilon_le_one M hM) ht hscale hcoeff

end NLA.FR05

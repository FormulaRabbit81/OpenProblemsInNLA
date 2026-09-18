/-
The source-faithful non-tail conditional small-ball branch of Lemma 3.6.

For a fixed radial coordinate and first phase, the deterministic centre is
controlled by the shifted scalar phase estimate. On its complement, the
complex-Gaussian tail is controlled by a variance-uniform projection bound.
No lower bound on the tail variance is imposed in this branch.
-/
import NLA.FR05.SourceScalarPhaseBridge
import NLA.FR05.GaussianProjectionUniformSmallBall
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The literal source Jacobian small-ball event over the second phase and
Gaussian tail, conditional on a radial coordinate and first phase. -/
def sourceNonTailConditionalSmallBallEvent {n : ℕ}
    (p q : Signal n) (sigma beta gamma S alpha u : ℝ) : Set (ℝ × Signal n) :=
  {x | x.1 ∈ Icc 0 (2 * Real.pi) ∧
    |sourceJacobianPhaseCenter sigma beta gamma alpha x.1 +
      Real.sqrt (2 / S) *
        (star (Complex.exp ((-alpha : ℂ) * Complex.I) • x.2) ⬝ᵥ
          (p + Complex.exp (((x.1 - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u}

theorem measurableSet_sourceNonTailConditionalSmallBallEvent {n : ℕ}
    (p q : Signal n) (sigma beta gamma S alpha u : ℝ) :
    MeasurableSet
      (sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u) := by
  unfold sourceNonTailConditionalSmallBallEvent
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc measurable_fst
  · change MeasurableSet
      ((fun x : ℝ × Signal n ↦
        |sourceJacobianPhaseCenter sigma beta gamma alpha x.1 +
          Real.sqrt (2 / S) *
            (star (Complex.exp ((-alpha : ℂ) * Complex.I) • x.2) ⬝ᵥ
              (p + Complex.exp (((x.1 - alpha : ℝ) : ℂ) * Complex.I) • q)).re|) ⁻¹'
        Iic u)
    apply MeasurableSet.preimage measurableSet_Iic
    have hcenter : Measurable
        (fun x : ℝ × Signal n ↦
          sourceJacobianPhaseCenter sigma beta gamma alpha x.1) :=
      (measurable_sourceJacobianPhaseCenter sigma beta gamma alpha).comp measurable_fst
    have htail : Measurable
        (fun x : ℝ × Signal n ↦
          Real.sqrt (2 / S) *
            (star (Complex.exp ((-alpha : ℂ) * Complex.I) • x.2) ⬝ᵥ
              (p + Complex.exp (((x.1 - alpha : ℝ) : ℂ) * Complex.I) • q)).re) := by
      fun_prop
    exact (hcenter.add htail).abs

/-- Rotate the first source phase out of the Gaussian tail and absorb the
real radial scale into the complex projection direction. -/
theorem sourceNonTailGaussianTerm_eq_real_dotProduct
    {n : ℕ} (p q w : Signal n) (S alpha phi : ℝ) :
    Real.sqrt (2 / S) *
        (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
          (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re =
      (star w ⬝ᵥ
        ((Real.sqrt (2 / S) : ℂ) •
          (Complex.exp ((alpha : ℂ) * Complex.I) •
            (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)))).re := by
  rw [phaseRotate_real_dotProduct]
  rw [dotProduct_smul, dotProduct_smul]
  conv_rhs => rw [smul_eq_mul, Complex.re_ofReal_mul]
  rw [dotProduct_smul]

/-- Conditional non-tail small-ball estimate for the literal source row.
The exceptional phase set has the source `sqrt(t)` bound, while every
remaining Gaussian-tail section has a uniform `u / t` bound. -/
theorem sourceUniformInterval_prod_sourceNonTailConditionalSmallBall_le
    {n : ℕ} (p q : Signal n) (sigma beta gamma S alpha u t : ℝ)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (standardComplexGaussianTail n))
        (sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let hphase : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let htail : IsProbabilityMeasure (standardComplexGaussianTail n) :=
    isProbabilityMeasure_standardComplexGaussianTail n
  apply @prod_measure_le_add_of_bad_sections ℝ (Signal n) _ _
    (sourceUniformInterval 0 (2 * Real.pi)) (standardComplexGaussianTail n) hphase htail
    (sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u)
    (measurableSet_sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u)
    (sourceJacobianPhaseCenterSublevel sigma beta gamma alpha t)
    (measurableSet_sourceJacobianPhaseCenterSublevel sigma beta gamma alpha t)
    (ENNReal.ofReal (2 * Real.sqrt (2 * t)))
    (ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)))
  · exact sourceUniformInterval_sourceJacobianPhaseCenterSublevel_le_two_sqrt_two_mul
      sigma beta gamma alpha t ht.le hcoeff
  · intro phi hphi
    by_cases hsupport : phi ∈ Icc 0 (2 * Real.pi)
    · have hnotle :
        ¬ |sourceJacobianPhaseCenter sigma beta gamma alpha phi| ≤ t := by
          intro hle
          exact hphi ⟨hsupport, hle⟩
      have hcentre : t ≤ |sourceJacobianPhaseCenter sigma beta gamma alpha phi| :=
        (lt_of_not_ge hnotle).le
      change standardComplexGaussianTail n
          {w : Signal n | phi ∈ Icc 0 (2 * Real.pi) ∧
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              Real.sqrt (2 / S) *
                (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                  (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u} ≤ _
      simp only [hsupport, true_and]
      let z : Signal n :=
        (Real.sqrt (2 / S) : ℂ) •
          (Complex.exp ((alpha : ℂ) * Complex.I) •
            (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q))
      have hset :
          {w : Signal n |
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              Real.sqrt (2 / S) *
                (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                  (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u} =
            {w : Signal n |
              |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
                (star w ⬝ᵥ z).re| ≤ u} := by
        ext w
        change
          |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
            Real.sqrt (2 / S) *
              (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u ↔
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              (star w ⬝ᵥ z).re| ≤ u
        dsimp [z]
        change
          |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
            Real.sqrt (2 / S) *
              (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u ↔
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              (star w ⬝ᵥ
                ((Real.sqrt (2 / S) : ℂ) •
                  (Complex.exp ((alpha : ℂ) * Complex.I) •
                    (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)))).re| ≤ u
        rw [sourceNonTailGaussianTerm_eq_real_dotProduct]
      rw [hset]
      exact standardComplexGaussianTail_real_dotProduct_abs_add_smallBall_uniform
        z (sourceJacobianPhaseCenter sigma beta gamma alpha phi) u t ht hcentre hscale
    · have hempty :
        {w : Signal n | (phi, w) ∈
          sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u} = ∅ := by
        ext w
        change (phi ∈ Icc 0 (2 * Real.pi) ∧
          |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
            Real.sqrt (2 / S) *
              (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u) ↔
          w ∈ (∅ : Set (Signal n))
        simp [hsupport]
      rw [hempty, measure_empty]
      exact bot_le

end NLA.FR05

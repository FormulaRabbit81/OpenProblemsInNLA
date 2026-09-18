/-
The scalar branch of the source Jacobian uses the phase difference
`beta - alpha`.  This file removes the fixed first-phase offset without
changing the coefficient energy, so the source-normalized phase small-ball
estimate applies directly to the literal shifted scalar term.
-/
import NLA.FR05.PhaseAbsolute
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The scalar part of (3.21) viewed as a function of the second source
phase while the first phase is fixed. -/
def sourceShiftedScalarPhase (sigma beta gamma alpha phi : ℝ) : ℝ :=
  sourceScalarPhase sigma beta gamma (phi - alpha)

/-- The cosine coefficient after removing a fixed phase offset. -/
def sourceScalarPhaseRotateBeta (beta gamma alpha : ℝ) : ℝ :=
  beta * Real.cos alpha + gamma * Real.sin alpha

/-- The sine coefficient after removing a fixed phase offset. -/
def sourceScalarPhaseRotateGamma (beta gamma alpha : ℝ) : ℝ :=
  gamma * Real.cos alpha - beta * Real.sin alpha

/-- The shifted scalar term is an unshifted source scalar phase term with
the rotated coefficients. -/
theorem sourceShiftedScalarPhase_eq_sourceScalarPhase
    (sigma beta gamma alpha phi : ℝ) :
    sourceShiftedScalarPhase sigma beta gamma alpha phi =
      sourceScalarPhase sigma
        (sourceScalarPhaseRotateBeta beta gamma alpha)
        (sourceScalarPhaseRotateGamma beta gamma alpha) phi := by
  unfold sourceShiftedScalarPhase sourceScalarPhase sourceScalarPhaseRotateBeta
    sourceScalarPhaseRotateGamma
  rw [Real.cos_sub, Real.sin_sub]
  ring

/-- Removing a phase offset preserves the two nonconstant coefficient
energies exactly. -/
theorem sourceScalarPhaseRotate_energy (beta gamma alpha : ℝ) :
    sourceScalarPhaseRotateBeta beta gamma alpha ^ 2 +
        sourceScalarPhaseRotateGamma beta gamma alpha ^ 2 =
      beta ^ 2 + gamma ^ 2 := by
  unfold sourceScalarPhaseRotateBeta sourceScalarPhaseRotateGamma
  have htrig := Real.cos_sq_add_sin_sq alpha
  ring_nf
  nlinarith

/-- The source-normalized shifted scalar phase sublevel event. -/
def sourceShiftedScalarPhaseSublevel
    (sigma beta gamma alpha t : ℝ) : Set ℝ :=
  {phi | phi ∈ Icc 0 (2 * Real.pi) ∧
    |sourceShiftedScalarPhase sigma beta gamma alpha phi| ≤ t}

theorem measurableSet_sourceShiftedScalarPhaseSublevel
    (sigma beta gamma alpha t : ℝ) :
    MeasurableSet (sourceShiftedScalarPhaseSublevel sigma beta gamma alpha t) := by
  unfold sourceShiftedScalarPhaseSublevel sourceShiftedScalarPhase sourceScalarPhase
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (((measurable_const.add
      (measurable_const.mul
        (Real.continuous_cos.comp (continuous_id.sub continuous_const)).measurable)).sub
      (measurable_const.mul
        (Real.continuous_sin.comp (continuous_id.sub continuous_const)).measurable)).abs)
    measurable_const

/-- The shifted sublevel event is literally the ordinary source scalar event
with its phase-rotated coefficients. -/
theorem sourceShiftedScalarPhaseSublevel_eq_sourceScalarPhaseSublevel
    (sigma beta gamma alpha t : ℝ) :
    sourceShiftedScalarPhaseSublevel sigma beta gamma alpha t =
      sourceScalarPhaseSublevel sigma
        (sourceScalarPhaseRotateBeta beta gamma alpha)
        (sourceScalarPhaseRotateGamma beta gamma alpha) t := by
  ext phi
  simp only [sourceShiftedScalarPhaseSublevel, sourceScalarPhaseSublevel,
    Set.mem_ofPred_eq]
  rw [sourceShiftedScalarPhase_eq_sourceScalarPhase]

/-- Uniform source phase control for the literal shifted scalar term.  The
constant agrees with the unshifted source-normalized estimate. -/
theorem sourceUniformInterval_sourceShiftedScalarPhaseSublevel_le_two_sqrt_two_mul
    (sigma beta gamma alpha t : ℝ) (ht : 0 ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceUniformInterval 0 (2 * Real.pi)
        (sourceShiftedScalarPhaseSublevel sigma beta gamma alpha t) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) := by
  rw [sourceShiftedScalarPhaseSublevel_eq_sourceScalarPhaseSublevel]
  apply sourceUniformInterval_sourceScalarPhaseSublevel_le_two_sqrt_two_mul
  · exact ht
  · nlinarith [sourceScalarPhaseRotate_energy beta gamma alpha]

end NLA.FR05

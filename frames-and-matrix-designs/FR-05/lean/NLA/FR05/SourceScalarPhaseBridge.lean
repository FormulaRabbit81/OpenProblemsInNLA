/-
Bridge the literal deterministic centre used by the source-row Jacobian to
the shifted scalar phase estimate.  This is the phase component of the
non-tail branch of Lemma 3.6; the Gaussian conditional step remains separate.
-/
import NLA.FR05.SourceTailConditional
import NLA.FR05.SourceScalarShift
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The literal deterministic source-row centre is the shifted source scalar
phase term. -/
theorem sourceJacobianPhaseCenter_apply_eq_sourceShiftedScalarPhase
    (sigma beta gamma alpha phi : ℝ) :
    sourceJacobianPhaseCenter sigma beta gamma alpha phi =
      sourceShiftedScalarPhase sigma beta gamma alpha phi := by
  rfl

/-- The source-row centre sublevel set on the second source phase. -/
def sourceJacobianPhaseCenterSublevel
    (sigma beta gamma alpha t : ℝ) : Set ℝ :=
  {phi | phi ∈ Icc 0 (2 * Real.pi) ∧
    |sourceJacobianPhaseCenter sigma beta gamma alpha phi| ≤ t}

theorem sourceJacobianPhaseCenterSublevel_eq_sourceShiftedScalarPhaseSublevel
    (sigma beta gamma alpha t : ℝ) :
    sourceJacobianPhaseCenterSublevel sigma beta gamma alpha t =
      sourceShiftedScalarPhaseSublevel sigma beta gamma alpha t := by
  ext phi
  simp only [sourceJacobianPhaseCenterSublevel,
    sourceShiftedScalarPhaseSublevel, Set.mem_ofPred_eq]
  rw [sourceJacobianPhaseCenter_apply_eq_sourceShiftedScalarPhase]

theorem measurableSet_sourceJacobianPhaseCenterSublevel
    (sigma beta gamma alpha t : ℝ) :
    MeasurableSet (sourceJacobianPhaseCenterSublevel sigma beta gamma alpha t) := by
  rw [sourceJacobianPhaseCenterSublevel_eq_sourceShiftedScalarPhaseSublevel]
  exact measurableSet_sourceShiftedScalarPhaseSublevel sigma beta gamma alpha t

/-- Uniform source-phase small-ball control for the literal deterministic
centre of the non-tail source Jacobian branch. -/
theorem sourceUniformInterval_sourceJacobianPhaseCenterSublevel_le_two_sqrt_two_mul
    (sigma beta gamma alpha t : ℝ) (ht : 0 ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceUniformInterval 0 (2 * Real.pi)
        (sourceJacobianPhaseCenterSublevel sigma beta gamma alpha t) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) := by
  rw [sourceJacobianPhaseCenterSublevel_eq_sourceShiftedScalarPhaseSublevel]
  exact sourceUniformInterval_sourceShiftedScalarPhaseSublevel_le_two_sqrt_two_mul
    sigma beta gamma alpha t ht hcoeff

end NLA.FR05

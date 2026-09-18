/-
Combine the two source-faithful conditional branches of Lemma 3.6.

For every unit source-Jacobian direction, its energy is either tail-dominated
or scalar-dominated. The preceding global branch estimates therefore yield a
single explicit row small-ball bound under the exact manuscript source law.
-/
import NLA.FR05.SourceTailGlobal
import NLA.FR05.SourceNonTailGlobal
import NLA.FR05.SourceJacobianEnergy
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The tail-dominated bound at the manuscript radial cutoff. -/
def sourceTailSmallBallBound (M : ℕ) (u t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (4 * t) +
    ENNReal.ofReal
      (2 * u * Real.sqrt (8 * (M : ℝ)) /
        (Real.sqrt (2 * Real.pi) * t))) +
    (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ))))

/-- The scalar-dominated source row bound. -/
def sourceNonTailSmallBallBound (u t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
    ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t))

/-- Exact source-law row small-ball estimate for a unit source-Jacobian
direction. This is the two-branch content of Lemma 3.6 before selecting a
common numerical scale for `t` and before the row-to-span argument. -/
theorem sourceCoordinateLaw_sourceM_sourceJacobianRowSmallBall_le_max
    {M n : ℕ} (hM : 1 ≤ M) (x : SourceJacobianVector n) (hunit : sourceJacobianEnergy x = 1)
    (u t : ℝ) (hu : 0 ≤ u) (ht : 0 < t) (hscale : 2 * u ≤ t) :
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
        (sourceRowJacobianSmallBallEvent
          (sourceJacobianP x) (sourceJacobianQ x) (x .sigma) (x .beta) (x .gamma) u) ≤
      max (sourceTailSmallBallBound M u t) (sourceNonTailSmallBallBound u t) := by
  rcases sourceJacobian_scalar_or_tail_tailEnergy_ge_quarter x hunit with htail | hscalar
  · calc
      sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
          (sourceRowJacobianSmallBallEvent
            (sourceJacobianP x) (sourceJacobianQ x) (x .sigma) (x .beta) (x .gamma) u) ≤
          sourceTailSmallBallBound M u t := by
            simpa only [sourceTailSmallBallBound] using
              (sourceCoordinateLaw_sourceM_sourceRowJacobianSmallBall_le
                hM (sourceJacobianP x) (sourceJacobianQ x)
                (x .sigma) (x .beta) (x .gamma) u t hu ht htail)
      _ ≤ max (sourceTailSmallBallBound M u t) (sourceNonTailSmallBallBound u t) :=
        le_max_left _ _
  · calc
      sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
          (sourceRowJacobianSmallBallEvent
            (sourceJacobianP x) (sourceJacobianQ x) (x .sigma) (x .beta) (x .gamma) u) ≤
          sourceNonTailSmallBallBound u t := by
            simpa only [sourceNonTailSmallBallBound] using
              (sourceCoordinateLaw_sourceM_sourceRowJacobianSmallBall_nonTail_le
                hM (sourceJacobianP x) (sourceJacobianQ x)
                (x .sigma) (x .beta) (x .gamma) u t ht hscale hscalar)
      _ ≤ max (sourceTailSmallBallBound M u t) (sourceNonTailSmallBallBound u t) :=
        le_max_right _ _

end NLA.FR05

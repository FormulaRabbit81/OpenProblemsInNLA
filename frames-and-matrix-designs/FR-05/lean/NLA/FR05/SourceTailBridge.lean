/-
Exact source-coordinate interpretation of the cutoff tail small-ball event.

The conditional estimate is stated on reassociated product coordinates for
Tonelli's theorem.  This bridge identifies it with the literal row form in
equation (3.21) on the support of the planted source law.
-/
import NLA.FR05.SourceTailConditional
import NLA.FR05.SourceRowBridge

set_option autoImplicit false
noncomputable section

open Set

namespace NLA.FR05

/-- On the support where a source coordinate tuple represents a planted row,
the reassociated cutoff event is exactly the literal source Jacobian
small-ball event, with its radial and phase cutoffs displayed explicitly. -/
theorem mem_sourceTailDominatedCutoffSmallBallEventOnCoordinates_iff
    {n : ℕ} (x : SourcePlantedCoordinates n) (hS : 0 < x.1.1)
    (hxi : |x.1.2.1| ≤ 1) (p q : Signal n) (σ b g B u : ℝ) :
    x ∈ sourceTailDominatedCutoffSmallBallEventOnCoordinates p q σ b g B u ↔
      0 < x.1.1 ∧ x.1.1 ≤ B ∧
        x.1.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
        x.1.2.2.2 ∈ Icc 0 (2 * Real.pi) ∧
        |sourceRowJacobianForm (sourceCoordinatesToPlantedRow x hS hxi)
          σ b g p q| ≤ u := by
  rfl

end NLA.FR05

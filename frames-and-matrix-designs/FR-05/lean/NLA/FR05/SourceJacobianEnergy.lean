/-
Source-coordinate energy bookkeeping for the two small-ball branches in
Lemma 3.6.  This is a thin bridge between the finite real Jacobian chart and
the `tailEnergy` notation used by the conditional Gaussian estimate.
-/
import NLA.FR05.SourceJacobianMatrix
import NLA.FR05.SmallBallAlgebra

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

/-- A unit real source-Jacobian direction is either tail-dominated, in the
notation required by the Gaussian conditional estimate, or has the scalar
energy required by the phase estimate. -/
theorem sourceJacobian_scalar_or_tail_tailEnergy_ge_quarter {n : ℕ}
    (x : SourceJacobianVector n) (hunit : sourceJacobianEnergy x = 1) :
    (1 / 4 : ℝ) ≤ tailEnergy (sourceJacobianP x) + tailEnergy (sourceJacobianQ x) ∨
      (3 / 4 : ℝ) ≤ x .sigma ^ 2 + x .beta ^ 2 + x .gamma ^ 2 := by
  simpa only [tailEnergy_eq_signalEnergy] using
    (sourceJacobian_scalar_or_tail_energy_ge_quarter x hunit)

/-- The same dichotomy for the unit Euclidean vectors used in the least-gain
formulation of the square source Jacobian. -/
theorem sourceJacobian_scalar_or_tail_tailEnergy_ge_quarter_of_norm_one {n : ℕ}
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) (hunit : ‖x‖ = 1) :
    (1 / 4 : ℝ) ≤ tailEnergy (sourceJacobianP (WithLp.ofLp x)) +
        tailEnergy (sourceJacobianQ (WithLp.ofLp x)) ∨
      (3 / 4 : ℝ) ≤ (WithLp.ofLp x) .sigma ^ 2 +
        (WithLp.ofLp x) .beta ^ 2 + (WithLp.ofLp x) .gamma ^ 2 := by
  simpa only [tailEnergy_eq_signalEnergy] using
    (sourceJacobian_scalar_or_tail_energy_ge_quarter_of_norm_one x hunit)

end NLA.FR05

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses the proved fixed-bound reflection evaluation and Mathlib's complex norm-square identity.

The same circle identity serves strict scalar normalization and the final
weighted polynomial equality, including zero polynomials and degree slack.
-/
import NLA.IE02.Reflection

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem circle_reflection_square (m : ℕ) (p : Poly) (hp : DegreeLE p m)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (p * conjReflect m p).eval z = z ^ m * ((‖p.eval z‖ ^ 2 : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
  have hnorm : p.eval z * star (p.eval z) = ((‖p.eval z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.sq_norm]
    exact Complex.mul_conj (p.eval z)
  rw [Polynomial.eval_mul, (reflection_evaluation m p hp z hz0).2 hz]
  calc
    p.eval z * (z ^ m * star (p.eval z)) = z ^ m * (p.eval z * star (p.eval z)) := by ring
    _ = z ^ m * ((‖p.eval z‖ ^ 2 : ℝ) : ℂ) := congrArg (fun v : ℂ => z ^ m * v) hnorm

#print axioms circle_reflection_square
#assert_trust kernel circle_reflection_square

end
end NLA.IE02

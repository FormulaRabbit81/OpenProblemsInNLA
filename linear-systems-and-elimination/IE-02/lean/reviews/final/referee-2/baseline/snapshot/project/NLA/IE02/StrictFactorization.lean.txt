/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses the proved effective polynomial, reciprocal inside factor, fixed-bound
circle reflection, and real-square-root weighted fold.

The complex multiplier is identified as a strictly positive real scalar at
z=1 before the real square-root normalization. The constant case is included.
-/
import NLA.IE02.EffectivePolynomial
import NLA.IE02.InsideFactor
import NLA.IE02.CircleSquares
import NLA.IE02.WeightedFold
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem strict_scalar_factorization {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (hq : ∀ j, DegreeLE (q j) m)
    (hno : ∀ z : ℂ, ‖z‖ = 1 → ∃ j, (q j).eval z ≠ 0) :
    ∃ h : Poly, DegreeLE h m ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖h.eval z‖ ^ 2 = sumSquares q z := by
  obtain ⟨ell, hell, hdegree, hzero, href, hcircle⟩ :=
    effective_factor_polynomial m q hq hno
  let P := effectivePolynomial m ell q
  let h0 := rootProduct (insideRoots P)
  obtain ⟨hhdegree, _hhzero, hhcircle, κ, _hκzero, hfactor⟩ :=
    reciprocal_inside_factor ell P hdegree hzero href (fun z hz => (hcircle z hz).2)
  have hh0 : DegreeLE h0 ell := hhdegree.le
  have hvalue (z : ℂ) (hz : ‖z‖ = 1) :
      (sumSquares q z : ℂ) = κ * ((‖h0.eval z‖ ^ 2 : ℝ) : ℂ) := by
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
    -- Only the nonzero circle power is canceled, including ell=0.
    apply mul_left_cancel₀ (pow_ne_zero ell hz0)
    calc
      z ^ ell * (sumSquares q z : ℂ) = P.eval z := (hcircle z hz).1.symm
      _ = κ * (h0 * conjReflect ell h0).eval z := by
        rw [hfactor, Polynomial.eval_mul, Polynomial.eval_C]
      _ = κ * (z ^ ell * ((‖h0.eval z‖ ^ 2 : ℝ) : ℂ)) := by
        rw [circle_reflection_square ell h0 hh0 z hz]
      _ = z ^ ell * (κ * ((‖h0.eval z‖ ^ 2 : ℝ) : ℂ)) := by ring
  let R : ℝ := ‖h0.eval 1‖ ^ 2
  have hRpos : 0 < R := sq_pos_of_pos (norm_pos_iff.mpr (hhcircle 1 (norm_one : ‖(1 : ℂ)‖ = 1)))
  have hQpos : 0 < sumSquares q 1 := sumSquares_pos q 1 (hno 1 (norm_one : ‖(1 : ℂ)‖ = 1))
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hRpos)
  let β : ℝ := sumSquares q 1 / R
  have hβpos : 0 < β := div_pos hQpos hRpos
  have hκ : κ = (β : ℂ) := by
    have h1 : (sumSquares q 1 : ℂ) = κ * (R : ℂ) := hvalue 1 (norm_one : ‖(1 : ℂ)‖ = 1)
    -- The denominator is a proved positive real square norm.
    calc
      κ = (sumSquares q 1 : ℂ) / (R : ℂ) := (eq_div_iff hRC).mpr h1.symm
      _ = (β : ℂ) := (Complex.ofReal_div (sumSquares q 1) R).symm
  have hreal (z : ℂ) (hz : ‖z‖ = 1) : sumSquares q z = β * ‖h0.eval z‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, ← hκ]
    exact hvalue z hz
  have hhbound : DegreeLE h0 m := hh0.trans (WithBot.coe_le_coe.mpr hell)
  -- The singleton instance reuses the actual nonnegative real-square-root scaling.
  have hfold := weighted_fold m (fun _ : Fin 1 => h0) (fun _ : Fin 1 => β)
    (fun _ => hhbound) (fun _ => hβpos.le)
  refine ⟨weightedFold β h0, hfold.1 0, ?_⟩
  intro z hz
  calc
    ‖(weightedFold β h0).eval z‖ ^ 2 = β * ‖h0.eval z‖ ^ 2 := by
      simpa only [sumSquares, Fin.sum_univ_one] using hfold.2 z
    _ = sumSquares q z := (hreal z hz).symm

#print axioms strict_scalar_factorization
#assert_trust kernel strict_scalar_factorization

end
end NLA.IE02

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

The universal positive-regularizer identity supplies infinitely many exact
characteristic-polynomial evaluations. No finite set of sampled shifts or
determinants is used to infer the polynomial identity.
-/
import NLA.SP15.ShiftedDeterminant
import NLA.SP15.CoefficientIdentity
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped Matrix

private theorem eval_charpoly_negative (G : Square 9) (a : ℂ) :
    G.charpoly.eval (-a) = -((a • (1 : Square 9) + G).det) := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hneg : (-a) • (1 : Square 9) - G = -(a • (1 : Square 9) + G) := by
    simp only [neg_smul, sub_eq_add_neg, neg_add]
  rw [hneg, Matrix.det_neg]
  norm_num

theorem equal_coefficients_gram_charpoly (x y : Parameters)
    (hx : x ∈ parameterBox) (hy : y ∈ parameterBox)
    (hxy : coefficients x = coefficients y) (z : ℂ) :
    (shiftedGram (constructedMatrix x) z).charpoly =
      (shiftedGram (constructedMatrix y) z).charpoly := by
  have hF (u s : ℂ) : coefficientDeterminant x u s = coefficientDeterminant y u s := by
    rw [coefficient_determinant_identity, coefficient_determinant_identity, hxy]
  have hdet (t : ℝ) (ht : 0 < t) :
      ((t : ℂ) • (1 : Square 9) + shiftedGram (constructedMatrix x) z).det =
        ((t : ℂ) • (1 : Square 9) + shiftedGram (constructedMatrix y) z).det := by
    rw [shifted_gram_determinant x hx z t ht, shifted_gram_determinant y hy z t ht, hF]
  let f : ℕ → ℂ := fun k => -((k + 1 : ℕ) : ℂ)
  have hf : Function.Injective f := by
    intro i j hij
    have hc : ((i + 1 : ℕ) : ℂ) = ((j + 1 : ℕ) : ℂ) := neg_injective hij
    exact Nat.add_right_cancel (Nat.cast_injective hc)
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem hf
  intro k
  -- Membership in the equality locus is exactly this evaluation at the chosen negative point.
  change (shiftedGram (constructedMatrix x) z).charpoly.eval (f k) =
    (shiftedGram (constructedMatrix y) z).charpoly.eval (f k)
  have ht : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos k
  have he := congrArg Neg.neg (hdet ((k + 1 : ℕ) : ℝ) ht)
  simpa only [f, eval_charpoly_negative, Complex.ofReal_natCast] using he

#print axioms equal_coefficients_gram_charpoly
#assert_trust kernel equal_coefficients_gram_charpoly

end
end NLA.SP15

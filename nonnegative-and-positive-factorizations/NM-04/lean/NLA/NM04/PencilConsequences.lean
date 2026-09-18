/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Algebraic consequences of the literal
minor relation, diagonal covariance and weighted principal-minor expansion.
These helpers do not assume a solution of the original problem: the full
contracts separately supply the relation and actual Sinkhorn scaling.
-/
import NLA.NM04.WeightedTransition
import NLA.NM04.DiagonalCovariance
import NLA.NM04.WeightedExpansion
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix

theorem weight_empty (m n : ℕ) :
    weight m n (emptyIndex (Tail m) (Tail n)) = 1 := by
  simp [weight, emptyIndex]

theorem weight_nonzero (m n : ℕ) : weight m n ≠ 0 := by
  intro h
  have he := congrFun h (emptyIndex (Tail m) (Tail n))
  rw [weight_empty] at he
  exact one_ne_zero he

theorem pencil_kernel_of_minor_relation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n)
    (hrel : ∀ I : Index m n,
      (m : ℝ) * minor (tailMatrix S) I +
        ((I.1.1.card : ℝ) * ((m : ℝ) + (n : ℝ)) - (m : ℝ) * (n : ℝ)) * delta S hm hn I +
        (n : ℝ) * raising (delta S hm hn) I - (m : ℝ) * lowering (delta S hm hn) I +
        (m : ℝ) * columnExchange (delta S hm hn) I +
        (n : ℝ) * rowExchange (delta S hm hn) I = 0) :
    (pencil S hm hn (S (firstIndex hm) (firstIndex hn))).mulVec (weight m n) = 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  funext I
  simp only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  rw [weighted_transition_action hm hn]
  change gamma S hm hn I * weight m n I +
    (S (firstIndex hm) (firstIndex hn) / (m : ℝ)) *
      (weight m n I * _) = 0
  calc
    _ = (S (firstIndex hm) (firstIndex hn) / (m : ℝ)) * weight m n I *
        ((m : ℝ) * minor (tailMatrix S) I +
          ((I.1.1.card : ℝ) * ((m : ℝ) + (n : ℝ)) - (m : ℝ) * (n : ℝ)) * delta S hm hn I +
          (n : ℝ) * raising (delta S hm hn) I - (m : ℝ) * lowering (delta S hm hn) I +
          (m : ℝ) * columnExchange (delta S hm hn) I +
          (n : ℝ) * rowExchange (delta S hm hn) I) := by
      unfold gamma
      field_simp
      ring
    _ = 0 := by rw [hrel I, mul_zero]

theorem transport_scaled_pencil_kernel {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (z : ℝ)
    (hnull : (pencil (diagonalScale A a b) hm hn z).mulVec (weight m n) = 0) :
    ∃ v : Index m n → ℝ, 0 < v (emptyIndex (Tail m) (Tail n)) ∧
      (pencil A hm hn z).mulVec v = 0 := by
  let D : Matrix (Index m n) (Index m n) ℝ := Matrix.diagonal (covarianceFactor a b hm hn)
  refine ⟨D.mulVec (weight m n), ?_, ?_⟩
  · change 0 < (Matrix.diagonal (covarianceFactor a b hm hn)).mulVec
      (weight m n) (emptyIndex (Tail m) (Tail n))
    rw [Matrix.mulVec_diagonal, weight_empty]
    simp only [covarianceFactor, emptyIndex, Finset.prod_empty, mul_one]
    exact mul_pos (ha (firstIndex hm)) (hb (firstIndex hn))
  · calc
      _ = (pencil A hm hn z * D).mulVec (weight m n) :=
        Matrix.mulVec_mulVec (weight m n) (pencil A hm hn z) D
      _ = (pencil (diagonalScale A a b) hm hn z).mulVec (weight m n) :=
        congrArg (fun M : Matrix (Index m n) (Index m n) ℝ => M.mulVec (weight m n))
          (diagonal_pencil_covariance hm hn A a b z).symm
      _ = 0 := hnull

theorem coefficient_sum_of_pencil_kernel {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (z : ℝ) (v : Index m n → ℝ)
    (hv : 0 < v (emptyIndex (Tail m) (Tail n)))
    (hnull : (pencil A hm hn z).mulVec v = 0) :
    (∑ E : Finset (Index m n),
      ((m : ℝ)⁻¹ • (HReal m n).submatrix
        (Subtype.val : E → Index m n) (Subtype.val : E → Index m n)).det *
      (∏ I ∈ E, delta A hm hn I) * (∏ I ∈ (Finset.univ \ E), gamma A hm hn I) *
      z ^ E.card) = 0 := by
  classical
  have hdet : (pencil A hm hn z).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hnull
      (mem_nonZeroDivisors_iff_ne_zero.mpr (ne_of_gt hv))
  have hp : Matrix.diagonal (gamma A hm hn) +
      z • (((m : ℝ)⁻¹ • HReal m n) * Matrix.diagonal (delta A hm hn)) =
      pencil A hm hn z := by
    ext I J
    simp only [pencil, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal,
      smul_eq_mul, div_eq_mul_inv]
    ring
  have he := weighted_principal_minor_expansion ((m : ℝ)⁻¹ • HReal m n)
    (gamma A hm hn) (delta A hm hn) z
  have hsum := he.symm.trans ((congrArg
    (fun M : Matrix (Index m n) (Index m n) ℝ => M.det) hp).trans hdet)
  have hsub (E : Finset (Index m n)) :
      (((m : ℝ)⁻¹ • HReal m n).submatrix
        (Subtype.val : E → Index m n) (Subtype.val : E → Index m n)) =
      (m : ℝ)⁻¹ • (HReal m n).submatrix
        (Subtype.val : E → Index m n) (Subtype.val : E → Index m n) := by
    rfl
  simpa only [hsub] using hsum

#print axioms weight_empty
#print axioms weight_nonzero
#print axioms pencil_kernel_of_minor_relation
#print axioms transport_scaled_pencil_kernel
#print axioms coefficient_sum_of_pencil_kernel
#assert_trust kernel weight_empty
#assert_trust kernel weight_nonzero
#assert_trust kernel pencil_kernel_of_minor_relation
#assert_trust kernel transport_scaled_pencil_kernel
#assert_trust kernel coefficient_sum_of_pencil_kernel

end
end NLA.NM04

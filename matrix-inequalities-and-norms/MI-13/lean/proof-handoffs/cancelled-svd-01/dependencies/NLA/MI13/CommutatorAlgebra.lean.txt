/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Nobori's question, Audenaert's refined
commutator theorem, and the repository reduction retain their attribution.

Exact Hilbert--Schmidt adjoint and conjugate-linear symmetry identities.
These finite algebraic statements include the empty square dimension.
-/
import NLA.MI13.Frobenius

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section
open scoped BigOperators Matrix

theorem commutator_inner {r : ℕ} (X Y Z : Square r) :
    hsInner (commutator X Y) Z = hsInner Y (commutator X.conjTranspose Z) := by
  simp only [hsInner, flatten_inner_eq_trace, commutator, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  · rw [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc]
    exact (Matrix.trace_mul_cycle' Y.conjTranspose Z X.conjTranspose).symm

theorem commutator_adjoint {r : ℕ} (X Y Z : Square r) :
    (commutatorOperator X).adjoint = commutatorOperator X.conjTranspose ∧
    hsInner (commutator X Y) Z = hsInner Y (commutator X.conjTranspose Z) ∧
    hsInner Y (commutatorT X Y) = ((frobeniusNorm (commutator X Y) ^ 2 : ℝ) : ℂ) := by
  have hadj : commutatorOperator X.conjTranspose = (commutatorOperator X).adjoint := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    let A : Square r := fun i j => x (i, j)
    let B : Square r := fun i j => y (i, j)
    have hA : flatten A = x := by ext ij; rfl
    have hB : flatten B = y := by ext ij; rfl
    rw [← hA, ← hB, commutatorOperator_flatten, commutatorOperator_flatten]
    simpa only [hsInner, Matrix.conjTranspose_conjTranspose] using
      commutator_inner X.conjTranspose A B
  refine ⟨hadj.symm, commutator_inner X Y Z, ?_⟩
  rw [commutatorT, ← commutator_inner]
  simp only [hsInner, inner_self_eq_norm_sq_to_K, frobeniusNorm,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]

theorem frobenius_conjTranspose {m n : ℕ} (A : Rect m n) :
    frobeniusNorm A.conjTranspose = frobeniusNorm A := by
  have hsq : frobeniusNorm A.conjTranspose ^ 2 = frobeniusNorm A ^ 2 := by
    rw [frobenius_norm_sq_eq_entries, frobenius_norm_sq_eq_entries]
    simp only [Matrix.conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  have hA := (frobenius_semantics A).2.2.1
  have hAt := (frobenius_semantics A.conjTranspose).2.2.1
  nlinarith

theorem commutator_conjugate_symmetry {r : ℕ} (X Y Z : Square r) (z : ℂ) :
    commutatorJ X (z • Y + Z) = star z • commutatorJ X Y + commutatorJ X Z ∧
    commutatorJ X (commutatorJ X Y) = -commutatorT X Y ∧
    commutatorT X (commutatorJ X Y) = commutatorJ X (commutatorT X Y) ∧
    hsInner Y (commutatorJ X Y) = 0 ∧
    frobeniusNorm (commutatorJ X Y) = frobeniusNorm (commutator X Y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [commutatorJ, commutator, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      smul_sub]
    abel
  · simp only [commutatorJ, commutatorT, commutator, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  · simp only [commutatorJ, commutatorT, commutator, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  · simp only [hsInner, flatten_inner_eq_trace, commutatorJ, commutator,
      Matrix.mul_sub, Matrix.trace_sub]
    apply sub_eq_zero.mpr
    exact Matrix.trace_mul_cycle' Y.conjTranspose X.conjTranspose Y.conjTranspose
  · have hJ : commutatorJ X Y = -(commutator X Y).conjTranspose := by
      simp only [commutatorJ, commutator, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_mul, neg_sub]
    rw [hJ, ← neg_one_smul ℂ,
      (frobenius_linear_bounds (commutator X Y).conjTranspose (0 : Square r) (-1)).1]
    simp only [norm_neg, norm_one, one_mul, frobenius_conjTranspose]

#print axioms commutator_adjoint
#assert_trust kernel commutator_adjoint
#print axioms commutator_conjugate_symmetry
#assert_trust kernel commutator_conjugate_symmetry

end
end NLA.MI13

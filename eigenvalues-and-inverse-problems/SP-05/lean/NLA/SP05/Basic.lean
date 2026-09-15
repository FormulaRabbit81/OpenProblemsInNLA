/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Certificates
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP05

lemma kronecker_columnVec {n : ℕ} (A B X : Mat n) :
    Matrix.kronecker A B *ᵥ columnVec X = columnVec (B * X * Aᵀ) := by
  exact Matrix.kronecker_mulVec_vec B X A

lemma commutation_mulVec {n : ℕ} (v : Vec n) :
    commutationMatrix n *ᵥ v = v ∘ Prod.swap := by
  ext i
  simp [commutationMatrix, Matrix.mulVec, dotProduct, Prod.ext_iff, Fintype.sum_prod_type, ite_and, Prod.swap]

lemma commutation_columnVec {n : ℕ} (X : Mat n) :
    commutationMatrix n *ᵥ columnVec X = columnVec Xᵀ := by
  rw [commutation_mulVec]
  rfl

lemma columnVec_dot_self {n : ℕ} (X : Mat n) :
    dotProduct (columnVec X) (columnVec X) = frobeniusSq X := by
  simp only [columnVec, dotProduct, Matrix.vec, Fintype.sum_prod_type, frobeniusSq,
    pow_two]
  exact Finset.sum_comm

lemma columnVec_ne_zero {n : ℕ} {X : Mat n} (hX : X ≠ 0) : columnVec X ≠ 0 := by
  intro h
  exact hX (Matrix.vec_eq_zero_iff.mp h)

lemma dot_self_pos {n : ℕ} {v : Vec n} (hv : v ≠ 0) : 0 < dotProduct v v := by
  simpa using (Matrix.dotProduct_star_self_pos_iff.mpr hv)

lemma skew_transpose (n : ℕ) : (skewExample n)ᵀ = -skewExample n := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, skewExample]
  split_ifs <;> simp_all

lemma skew_frobenius (n : ℕ) (hn : 2 ≤ n) : frobeniusSq (skewExample n) = 2 := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  have hform : skewExample n = fun i j =>
      if i = a then (if j = b then 1 else 0) else
      if i = b then (if j = a then -1 else 0) else 0 := by
    ext i j
    simp only [skewExample, Fin.ext_iff]
    dsimp [a, b]
    split_ifs <;> simp_all
  rw [frobeniusSq, hform]
  simp only [ite_pow, one_pow, neg_one_sq, zero_pow (by decide : 2 ≠ 0)]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  have hind (x : Fin n) : (if x = a then (1 : ℝ) else if x = b then 1 else 0) =
      (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hind]
  norm_num [Finset.sum_add_distrib]

lemma skew_frobenius_pos (n : ℕ) (hn : 2 ≤ n) : 0 < frobeniusSq (skewExample n) := by
  rw [skew_frobenius n hn]
  exact skew_norm_positive_certificate

lemma skew_ne_zero (n : ℕ) (hn : 2 ≤ n) : skewExample n ≠ 0 := by
  intro h
  have hp := skew_frobenius_pos n hn
  simp [h, frobeniusSq] at hp

end NLA.SP05

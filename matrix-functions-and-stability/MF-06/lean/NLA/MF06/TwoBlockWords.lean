/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The off-diagonal block is an explicit finite sum over the positions of the
original chronological word. No independent choices of the two diagonal
words are introduced. All dimensions, including zero, are allowed here.
-/
import NLA.MF06.WordImages
import Mathlib.Data.Matrix.Block
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

/-- The actual upper two-block matrix, reindexed into the canonical `Fin` space. -/
def twoBlockMatrix {m n : ℕ} (B : Square m) (D : Matrix (Fin m) (Fin n) ℂ)
    (C : Square n) : Square (m + n) :=
  (Matrix.fromBlocks B D 0 C).submatrix
    (finSumFinEquiv (m := m) (n := n)).symm
    (finSumFinEquiv (m := m) (n := n)).symm

lemma twoBlockMatrix_one {m n : ℕ} :
    twoBlockMatrix (1 : Square m) 0 (1 : Square n) = 1 := by
  unfold twoBlockMatrix
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one _ (finSumFinEquiv (m := m) (n := n)).symm.injective

lemma twoBlockMatrix_mul {m n : ℕ} (B B' : Square m)
    (D D' : Matrix (Fin m) (Fin n) ℂ) (C C' : Square n) :
    twoBlockMatrix B D C * twoBlockMatrix B' D' C' =
      twoBlockMatrix (B * B') (B * D' + D * C') (C * C') := by
  unfold twoBlockMatrix
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The sole transition occurs at `i`, after the prefix and before the suffix. -/
def offDiagonalSum {α : Type*} {m n : ℕ} (f : α → Square m)
    (g : α → Square n) (h : α → Matrix (Fin m) (Fin n) ℂ) (w : List α) :
    Matrix (Fin m) (Fin n) ℂ :=
  ∑ i : Fin w.length,
    matrixProduct ((w.drop (i.val + 1)).map f) * h (w.get i) *
      matrixProduct ((w.take i.val).map g)

lemma offDiagonalSum_nil {α : Type*} {m n : ℕ} (f : α → Square m)
    (g : α → Square n) (h : α → Matrix (Fin m) (Fin n) ℂ) :
    offDiagonalSum f g h [] = 0 := by
  simp only [offDiagonalSum, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]

lemma offDiagonalSum_cons {α : Type*} {m n : ℕ} (f : α → Square m)
    (g : α → Square n) (h : α → Matrix (Fin m) (Fin n) ℂ) (A : α) (w : List α) :
    offDiagonalSum f g h (A :: w) =
      matrixProduct (w.map f) * h A + offDiagonalSum f g h w * g A := by
  simp only [offDiagonalSum, List.length_cons, Fin.sum_univ_succ,
    Fin.val_zero, zero_add, List.drop_succ_cons, List.drop_zero,
    List.get_cons_zero, List.take_zero, List.map_nil, matrixProduct_nil,
    Matrix.mul_one, Fin.val_succ, List.get_cons_succ', List.take_succ_cons,
    List.map_cons, matrixProduct_cons]
  rw [Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (Matrix.mul_assoc _ _ _).symm

/-- Exact finite Duhamel expansion, with the frozen chronological convention. -/
lemma twoBlock_matrixProduct {α : Type*} {m n : ℕ} (f : α → Square m)
    (g : α → Square n) (h : α → Matrix (Fin m) (Fin n) ℂ) (w : List α) :
    matrixProduct (w.map (fun A => twoBlockMatrix (f A) (h A) (g A))) =
      twoBlockMatrix (matrixProduct (w.map f)) (offDiagonalSum f g h w)
        (matrixProduct (w.map g)) := by
  induction w with
  | nil =>
      simp only [List.map_nil, matrixProduct_nil, offDiagonalSum_nil, twoBlockMatrix_one]
  | cons A w ih =>
      simp only [List.map_cons, matrixProduct_cons, ih, twoBlockMatrix_mul,
        offDiagonalSum_cons]

#print axioms twoBlock_matrixProduct
#assert_trust kernel twoBlock_matrixProduct

end NLA.MF06

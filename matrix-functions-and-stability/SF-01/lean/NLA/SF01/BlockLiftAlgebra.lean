/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Exact generic block and rectangular-lift algebra. Both index dimensions may
be zero; no spectral, positivity or nonsingularity premise is hidden here.
-/
import NLA.SF01.Definitions
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.Ext

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

abbrev LiftedSquare (r n : ℕ) := Matrix (Fin r × Fin n) (Fin r × Fin n) ℝ

def blockFamily {r n : ℕ} (F : Fin r → Square n) : LiftedSquare r n :=
  Matrix.of (fun i j => if i.1 = j.1 then F i.1 i.2 j.2 else 0)

def scalarLift {r n : ℕ} (u : Vector r) : Matrix (Fin r × Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => u i.1 * (1 : Square n) i.2 j)

def matrixLift {r n : ℕ} (Q : Square r) : LiftedSquare r n :=
  Matrix.kronecker Q (1 : Square n)

lemma blockFamily_eq_reindex {r n : ℕ} (F : Fin r → Square n) :
    blockFamily F = Matrix.reindex (Equiv.prodComm (Fin n) (Fin r))
      (Equiv.prodComm (Fin n) (Fin r)) (Matrix.blockDiagonal F) := by
  rfl

lemma blockFamily_mul {r n : ℕ} (F G : Fin r → Square n) :
    blockFamily (fun i => F i * G i) = blockFamily F * blockFamily G := by
  simp only [blockFamily_eq_reindex, Matrix.blockDiagonal_mul]
  exact (Matrix.reindexRingEquiv ℝ (Equiv.prodComm (Fin n) (Fin r))).map_mul
    (Matrix.blockDiagonal F) (Matrix.blockDiagonal G)

lemma blockFamily_one {r n : ℕ} :
    blockFamily (fun _ : Fin r => (1 : Square n)) = 1 := by
  rw [blockFamily_eq_reindex]
  change (Matrix.reindexRingEquiv ℝ (Equiv.prodComm (Fin n) (Fin r)))
    (Matrix.blockDiagonal (1 : Fin r → Square n)) = 1
  rw [Matrix.blockDiagonal_one, map_one]

lemma blockFamily_unit_inverse {r n : ℕ} (F : Fin r → Square n)
    (hF : ∀ i, IsUnit (F i)) :
    IsUnit (blockFamily F) ∧
      (blockFamily F)⁻¹ = blockFamily (fun i => (F i)⁻¹) := by
  have hmul : blockFamily F * blockFamily (fun i => (F i)⁻¹) = 1 := by
    rw [← blockFamily_mul]
    have hblocks : (fun i => F i * (F i)⁻¹) =
        (fun _ : Fin r => (1 : Square n)) := by
      funext i
      exact Matrix.mul_nonsing_inv (F i) ((Matrix.isUnit_iff_isUnit_det _).mp (hF i))
    rw [hblocks, blockFamily_one]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse hmul), Matrix.inv_eq_right_inv hmul⟩

lemma matrixLift_transpose {r n : ℕ} (Q : Square r) :
    (matrixLift (n := n) Q).transpose = matrixLift (n := n) Q.transpose := by
  simpa only [matrixLift, Matrix.kronecker, Matrix.transpose_one] using
    (Matrix.kroneckerMap_transpose (fun (x y : ℝ) => x * y) Q (1 : Square n)).symm

lemma matrixLift_orthogonal {r n : ℕ} (Q : Square r) (hQ : IsOrthogonal Q) :
    (matrixLift (n := n) Q).transpose * matrixLift (n := n) Q = 1 ∧
      matrixLift (n := n) Q * (matrixLift (n := n) Q).transpose = 1 := by
  simp only [matrixLift_transpose]
  constructor
  · calc
      matrixLift (n := n) Q.transpose * matrixLift (n := n) Q =
          Matrix.kronecker (Q.transpose * Q) ((1 : Square n) * 1) :=
        (Matrix.mul_kronecker_mul Q.transpose Q (1 : Square n) (1 : Square n)).symm
      _ = 1 := by
        rw [hQ.1, Matrix.mul_one]
        exact Matrix.one_kronecker_one
  · calc
      matrixLift (n := n) Q * matrixLift (n := n) Q.transpose =
          Matrix.kronecker (Q * Q.transpose) ((1 : Square n) * 1) :=
        (Matrix.mul_kronecker_mul Q Q.transpose (1 : Square n) (1 : Square n)).symm
      _ = 1 := by
        rw [hQ.2, Matrix.mul_one]
        exact Matrix.one_kronecker_one

lemma scalarLift_outer {r n : ℕ} (u : Vector r) :
    scalarLift (n := n) u * (scalarLift (n := n) u).transpose =
      Matrix.kronecker (Matrix.of (fun i j => u i * u j)) (1 : Square n) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hij : i = j
  · subst j
    simp [scalarLift, Matrix.mul_apply, Matrix.one_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, mul_ite, ite_mul]
  · simp [scalarLift, Matrix.mul_apply, Matrix.one_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, hij, Ne.symm hij, mul_ite, ite_mul]

lemma matrixLift_transpose_scalarLift {r n : ℕ} (Q : Square r) (u : Vector r) :
    (matrixLift (n := n) Q).transpose * scalarLift (n := n) u =
      scalarLift (n := n) (Q.transpose *ᵥ u) := by
  rw [matrixLift_transpose]
  ext ⟨a, i⟩ j
  by_cases hij : i = j
  · subst j
    simp [matrixLift, scalarLift, Matrix.mul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Matrix.mulVec, dotProduct, mul_ite, ite_mul, mul_assoc]
  · simp [matrixLift, scalarLift, Matrix.mul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
      hij, Ne.symm hij, mul_ite, ite_mul]

lemma scalarLift_blockFamily_compression {r n : ℕ} (u : Vector r)
    (F : Fin r → Square n) :
    (scalarLift (n := n) u).transpose * blockFamily F * scalarLift (n := n) u =
      ∑ i : Fin r, u i ^ 2 • F i := by
  have hleft : (scalarLift (n := n) u).transpose * blockFamily F =
      Matrix.of (fun i j => u j.1 * F j.1 i j.2) := by
    ext i ⟨a, j⟩
    simp [scalarLift, blockFamily, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_ite, ite_mul]
  rw [hleft]
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, scalarLift, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp [Matrix.one_apply, mul_ite, ite_mul, pow_two, mul_assoc, mul_left_comm, mul_comm]

end
end NLA.SF01

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Actual block units and their inverses, with all shifts proved admissible.
The generic block/lift algebra is kept opaque across this module boundary.
-/
import NLA.SF01.BlockLiftAlgebra
import NLA.SF01.PoleResidues
import NLA.SF01.RidgeComparison

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma baseBlock_blocks {n : ℕ} (d : RidgeData) (A : Square n) :
    baseBlock d A = blockFamily (fun i => shifted A (poleOffsets d i)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp [baseBlock, blockFamily, Matrix.kronecker_apply, Matrix.diagonal_apply, shifted]
  · simp [baseBlock, blockFamily, Matrix.kronecker_apply, Matrix.diagonal_apply, hij]

lemma poleBlock_rank_update {n : ℕ} (d : RidgeData) (A : Square n) :
    poleBlock d A = baseBlock d A +
      d.b⁻¹ • (scalarLift (n := n) (poleVector d) *
        (scalarLift (n := n) (poleVector d)).transpose) := by
  rw [scalarLift_outer]
  have ha := Matrix.add_kronecker (Matrix.diagonal (poleOffsets d))
    (d.b⁻¹ • Matrix.of (fun i j => poleVector d i * poleVector d j)) (1 : Square n)
  have hs := Matrix.smul_kronecker d.b⁻¹
    (Matrix.of (fun i j => poleVector d i * poleVector d j)) (1 : Square n)
  unfold poleBlock baseBlock poleMatrix
  simp only [Matrix.kronecker]
  rw [ha, hs]
  exact (add_assoc _ _ _).symm

lemma poleBlock_diagonalized {n : ℕ} (d : RidgeData)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam) (A : Square n) :
    poleBlock d A = matrixLift (n := n) Q *
      blockFamily (fun i => shifted A (lam i)) * (matrixLift (n := n) Q).transpose := by
  have hblocks : blockFamily (fun i => shifted A (lam i)) =
      Matrix.kronecker (1 : Square (d.size + 1)) A +
        Matrix.kronecker (Matrix.diagonal lam) (1 : Square n) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      simp [blockFamily, Matrix.kronecker_apply, Matrix.diagonal_apply, shifted]
    · simp [blockFamily, Matrix.kronecker_apply, Matrix.diagonal_apply, hij]
  have hm (P R : Square (d.size + 1)) (X Y : Square n) :
      Matrix.kronecker P X * Matrix.kronecker R Y =
        Matrix.kronecker (P * R) (X * Y) :=
    (Matrix.mul_kronecker_mul P R X Y).symm
  rw [hblocks, matrixLift_transpose]
  simp only [poleBlock, matrixLift, Matrix.mul_add, Matrix.add_mul]
  rw [hm Q 1 1 A, hm (Q * 1) Q.transpose (1 * A) 1,
    hm Q (Matrix.diagonal lam) 1 1,
    hm (Q * Matrix.diagonal lam) Q.transpose (1 * 1) 1]
  simp only [mul_one, one_mul, hdiag.1.2, ← hdiag.2.2]

theorem reciprocal_blocks_isUnit (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    IsUnit (baseBlock d A) ∧ IsUnit (poleBlock d A) := by
  have hoff : ∀ i : Fin (d.size + 1), 0 ≤ poleOffsets d i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_refl 0
    · exact (hd.2.2.1 j).le
  have hbase : IsUnit (baseBlock d A) := by
    rw [baseBlock_blocks]
    exact (blockFamily_unit_inverse _
      (fun i => (H_shift_structure hn A hA (poleOffsets d i) (hoff i)).2.1)).1
  obtain ⟨Q, lam, hdiag⟩ := pole_diagonalization_exists d hd
  have hV := matrixLift_orthogonal (n := n) Q hdiag.1
  have hD : IsUnit (blockFamily (fun i => shifted A (lam i))) :=
    (blockFamily_unit_inverse _
      (fun i => (H_shift_structure hn A hA (lam i) (hdiag.2.1 i).le).2.1)).1
  have hVu : IsUnit (matrixLift (n := n) Q) :=
    IsUnit.of_mul_eq_one _ hV.2
  have hVtu : IsUnit (matrixLift (n := n) Q).transpose :=
    IsUnit.of_mul_eq_one _ hV.1
  refine ⟨hbase, ?_⟩
  rw [poleBlock_diagonalized d Q lam hdiag A]
  exact (hVu.mul hD).mul hVtu

lemma poleBlock_inverse_diagonalized (d : RidgeData) (hd : ValidData d)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    (poleBlock d A)⁻¹ = matrixLift (n := n) Q *
      blockFamily (fun i => (shifted A (lam i))⁻¹) *
        (matrixLift (n := n) Q).transpose := by
  let V := matrixLift (n := n) Q
  let D := blockFamily (fun i => shifted A (lam i))
  let E := blockFamily (fun i => (shifted A (lam i))⁻¹)
  have hV : V.transpose * V = 1 ∧ V * V.transpose = 1 :=
    matrixLift_orthogonal Q hdiag.1
  have hD := blockFamily_unit_inverse (fun i => shifted A (lam i))
    (fun i => (H_shift_structure hn A hA (lam i) (hdiag.2.1 i).le).2.1)
  have hDE : D * E = 1 := by
    change blockFamily (fun i => shifted A (lam i)) * E = 1
    rw [show E = (blockFamily (fun i => shifted A (lam i)))⁻¹ from hD.2.symm]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hD.1)
  apply Matrix.inv_eq_right_inv
  rw [poleBlock_diagonalized d Q lam hdiag A]
  change (V * D * V.transpose) * (V * E * V.transpose) = 1
  calc
    (V * D * V.transpose) * (V * E * V.transpose) =
        V * (D * (V.transpose * V) * E) * V.transpose := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hV.1, mul_one, hDE, mul_one, hV.2]

end
end NLA.SF01

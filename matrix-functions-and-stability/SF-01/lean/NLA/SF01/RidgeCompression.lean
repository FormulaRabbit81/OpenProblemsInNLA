/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Finite compression of the actual base inverse and its invertible ridge factor.
No conditional inverse identity is promoted to a public premise.
-/
import NLA.SF01.ReciprocalBlocks
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

def baseCompression {n : ℕ} (d : RidgeData) (A : Square n) : Square n :=
  (scalarLift (n := n) (poleVector d)).transpose * (baseBlock d A)⁻¹ *
    scalarLift (n := n) (poleVector d)

def poleCompression {n : ℕ} (d : RidgeData) (A : Square n) : Square n :=
  (scalarLift (n := n) (poleVector d)).transpose * (poleBlock d A)⁻¹ *
    scalarLift (n := n) (poleVector d)

def compressedFactor {n : ℕ} (d : RidgeData) (A : Square n) : Square n :=
  d.b • (1 : Square n) + baseCompression d A

lemma baseCompression_expansion (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    baseCompression d A = d.a • A⁻¹ +
      ∑ j : Fin d.size, d.weights j • (shifted A (d.poles j))⁻¹ := by
  have hoff : ∀ i : Fin (d.size + 1), 0 ≤ poleOffsets d i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_refl 0
    · exact (hd.2.2.1 j).le
  have hblocks := blockFamily_unit_inverse (fun i => shifted A (poleOffsets d i))
    (fun i => (H_shift_structure hn A hA (poleOffsets d i) (hoff i)).2.1)
  unfold baseCompression
  rw [baseBlock_blocks, hblocks.2, scalarLift_blockFamily_compression, Fin.sum_univ_succ]
  simp only [poleVector, poleOffsets, Fin.cases_zero, Fin.cases_succ,
    Real.sq_sqrt hd.1.le, shifted, zero_smul, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.sq_sqrt (hd.2.2.2 j)]

lemma compressedFactor_structure (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    IsUnit (compressedFactor d A) ∧
      ridgeEval d A = A * compressedFactor d A ∧
        (compressedFactor d A)⁻¹ = (ridgeEval d A)⁻¹ * A := by
  have hAu := (H_positive_weight hn A hA.1).1
  have hAinv : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hAu)
  have hAF : ridgeEval d A = A * compressedFactor d A := by
    rw [compressedFactor, baseCompression_expansion d hd hn A hA]
    simp only [Matrix.mul_add, Matrix.mul_smul, mul_one, Finset.mul_sum, hAinv,
      ridgeEval]
    abel
  obtain ⟨_, _, _, _, _, _, hR⟩ := ridge_comparison_preserver d hd hn A hA
  have hF : IsUnit (compressedFactor d A) :=
    isUnit_of_mul_isUnit_right (hAF ▸ hR)
  refine ⟨hF, hAF, ?_⟩
  apply Matrix.inv_eq_left_inv
  calc
    ((ridgeEval d A)⁻¹ * A) * compressedFactor d A =
        (ridgeEval d A)⁻¹ * ridgeEval d A := by rw [Matrix.mul_assoc, ← hAF]
    _ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hR)

end
end NLA.SF01

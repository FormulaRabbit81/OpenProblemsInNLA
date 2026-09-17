/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Every supplied orthogonal pole diagonalization yields the same actual
matrix reciprocal. Zero residues and repeated poles require no cancellation.
-/
import NLA.SF01.PoleCompression

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma reciprocalEval_complement (d : RidgeData) (hd : ValidData d)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    reciprocalEval d Q lam A =
      d.b⁻¹ • (1 : Square n) - (d.b⁻¹) ^ 2 • poleCompression d A := by
  have hterm : ∀ i : Fin (d.size + 1),
      reciprocalWeights d Q lam i * lam i =
        (d.b⁻¹) ^ 2 * spectralCoordinates d Q i ^ 2 := by
    intro i
    unfold reciprocalWeights
    field_simp [hd.2.1.ne', (hdiag.2.1 i).ne'] <;> ring
  calc
    reciprocalEval d Q lam A = ∑ i : Fin (d.size + 1),
        (reciprocalWeights d Q lam i • (1 : Square n) -
          ((d.b⁻¹) ^ 2 * spectralCoordinates d Q i ^ 2) • (shifted A (lam i))⁻¹) := by
      unfold reciprocalEval
      apply Finset.sum_congr rfl
      intro i _
      rw [shifted_right_resolvent A (lam i)
        (H_shift_structure hn A hA (lam i) (hdiag.2.1 i).le).2.1,
        smul_sub, smul_smul, hterm i]
    _ = d.b⁻¹ • (1 : Square n) - (d.b⁻¹) ^ 2 • poleCompression d A := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul,
        reciprocalWeights_sum d hd Q lam hdiag,
        poleCompression_spectral d hd Q lam hdiag hn A hA,
        Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]

theorem matrix_reciprocal_identity (d : RidgeData) (hd : ValidData d)
    (Q : Square (d.size + 1)) (lam : Fin (d.size + 1) → ℝ)
    (hdiag : PoleDiagonalization d Q lam)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    (ridgeEval d A)⁻¹ * A = reciprocalEval d Q lam A := by
  calc
    (ridgeEval d A)⁻¹ * A = (compressedFactor d A)⁻¹ :=
      (compressedFactor_structure d hd hn A hA).2.2.symm
    _ = d.b⁻¹ • (1 : Square n) - (d.b⁻¹) ^ 2 • poleCompression d A :=
      compressedFactor_inverse_complement d hd hn A hA
    _ = reciprocalEval d Q lam A :=
      (reciprocalEval_complement d hd Q lam hdiag hn A hA).symm

end
end NLA.SF01

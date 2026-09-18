/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The reused coordinate operator estimates retain their MF07/Colbrook attribution.

Positive powers of a scalar give a literal diagonal inverse pair. Conjugation
preserves the diagonal blocks and shrinks each strict upper block. The norm
estimate is entrywise and symbolic, with no finite dimension computation.
-/
import NLA.MF06.BlockDiagonalEnvelope
import NLA.MF06.SimilaritySemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

def blockConjugate {d r : ℕ} (b : Fin d → Fin r) (t : ℝ) (A : Square d) : Square d :=
  inverseDiagonalWeights (fun u => t ^ (b u).val) * A *
    diagonalWeights (fun u => t ^ (b u).val)

lemma blockConjugate_apply {d r : ℕ} (b : Fin d → Fin r) (t : ℝ)
    (A : Square d) (u v : Fin d) :
    blockConjugate b t A u v = ((t ^ (b u).val)⁻¹ : ℂ) * A u v * (t ^ (b v).val : ℂ) := by
  simp only [blockConjugate, inverseDiagonalWeights, diagonalWeights,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_pow]

lemma blockConjugate_entry_of_le {d r : ℕ} (b : Fin d → Fin r) (t : ℝ)
    (ht : t ≠ 0) (A : Square d) (u v : Fin d) (huv : b u ≤ b v) :
    blockConjugate b t A u v = (t ^ ((b v).val - (b u).val) : ℂ) * A u v := by
  rw [blockConjugate_apply,
    pow_sub₀ (t : ℂ) (Complex.ofReal_ne_zero.mpr ht) (Fin.le_def.mp huv)]
  ring

/-- All entries, including zero lower blocks and unchanged diagonal blocks,
obey one uniform error estimate. -/
lemma blockConjugate_error_entry {d r : ℕ} (b : Fin d → Fin r) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (A : Square d)
    (hA : IsUpperBlockTriangular b A) (u v : Fin d) :
    ‖(blockConjugate b t A - blockDiagonalPart b A) u v‖ ≤ t * ‖A u v‖ := by
  rcases lt_trichotomy (b u) (b v) with huv | huv | hvu
  · have hne : (b v).val - (b u).val ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt (Fin.lt_def.mp huv))
    rw [Matrix.sub_apply, blockConjugate_entry_of_le b t ht.ne' A u v huv.le]
    simp only [blockDiagonalPart, if_neg (ne_of_lt huv), sub_zero, norm_mul,
      norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_right (pow_le_of_le_one ht.le ht1 hne) (norm_nonneg _)
  · have he : blockConjugate b t A u v = A u v := by
      rw [blockConjugate_entry_of_le b t ht.ne' A u v huv.le, huv]
      simp only [Nat.sub_self, pow_zero, one_mul]
    rw [Matrix.sub_apply, he]
    simp only [blockDiagonalPart, if_pos huv, sub_self, norm_zero]
    exact mul_nonneg ht.le (norm_nonneg _)
  · have hz := hA u v hvu
    simp only [Matrix.sub_apply, blockConjugate_apply, blockDiagonalPart,
      if_neg (ne_of_gt hvu), hz, mul_zero, zero_mul, sub_zero, norm_zero, le_refl]

lemma blockConjugate_error_norm {d r : ℕ} (b : Fin d → Fin r) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (A : Square d)
    (hA : IsUpperBlockTriangular b A) (L : ℝ) (hL : 0 ≤ L)
    (hAL : spectralNorm A ≤ L) :
    spectralNorm (blockConjugate b t A - blockDiagonalPart b A) ≤ (d : ℝ) * L * t := by
  calc
    spectralNorm (blockConjugate b t A - blockDiagonalPart b A) ≤ (d : ℝ) * (t * L) := by
      apply spectralNorm_le_card_mul_entry_bound _ (t * L) (mul_nonneg ht.le hL)
      intro u v
      exact (blockConjugate_error_entry b t ht ht1 A hA u v).trans
        (mul_le_mul_of_nonneg_left ((spectralNorm_entry_bound A u v).trans hAL) ht.le)
    _ = (d : ℝ) * L * t := by ring

lemma blockConjugate_semantics {d r : ℕ} (hd : 1 ≤ d) (b : Fin d → Fin r)
    (t : ℝ) (ht : 0 < t) (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty) :
    IsCompact ((blockConjugate b t) '' M) ∧ ((blockConjugate b t) '' M).Nonempty ∧
      jointSpectralRadius ((blockConjugate b t) '' M) = jointSpectralRadius M := by
  have hi := diagonal_inverse (fun u : Fin d => t ^ (b u).val)
    (fun u => pow_ne_zero _ ht.ne')
  have h := similarity_semantics hd (diagonalWeights (fun u : Fin d => t ^ (b u).val))
    (inverseDiagonalWeights (fun u : Fin d => t ^ (b u).val)) hi.1 hi.2 M hM hneM
  exact ⟨h.1, h.2.1, h.2.2.1⟩

#print axioms blockConjugate_error_norm
#assert_trust kernel blockConjugate_error_norm
#print axioms blockConjugate_semantics
#assert_trust kernel blockConjugate_semantics

end NLA.MF06

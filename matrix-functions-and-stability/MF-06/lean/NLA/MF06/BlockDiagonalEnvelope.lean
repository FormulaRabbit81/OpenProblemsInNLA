/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The reused operator bounds and arbitrary-radius exponential envelopes retain
the Matthew J. Colbrook attribution in the unchanged MF05/MF07 development.

Zeroing the off-diagonal blocks is a literal coordinate operation. Its words
retain the same original letters in every block. Finitely many actual diagonal
envelopes then give one common exponential bound without enumerating words.
-/
import NLA.MF06.BlockLowerRadius

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

def blockDiagonalPart {d r : ℕ} (b : Fin d → Fin r) (A : Square d) : Square d :=
  fun u v => if b u = b v then A u v else 0

lemma blockDiagonalPart_upper {d r : ℕ} (b : Fin d → Fin r) (A : Square d) :
    IsUpperBlockTriangular b (blockDiagonalPart b A) := by
  intro u v huv
  exact if_neg (ne_of_gt huv)

lemma blockMatrix_blockDiagonalPart {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (A : Square d) : blockMatrix b i (blockDiagonalPart b A) = blockMatrix b i A := by
  ext u v
  simp only [blockMatrix, blockDiagonalPart, blockCoordinate_label, ite_true]

lemma blockDiagonalPart_product_support {d r : ℕ} (b : Fin d → Fin r)
    (w : List (Square d)) :
    ∀ u v, b u ≠ b v → matrixProduct (w.map (blockDiagonalPart b)) u v = 0 := by
  induction w with
  | nil =>
      intro u v huv
      have hne : u ≠ v := fun h => huv (congrArg b h)
      simp only [List.map_nil, matrixProduct_nil, Matrix.one_apply, if_neg hne]
  | cons A w ih =>
      intro u v huv
      rw [List.map_cons, matrixProduct_cons, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j _
      by_cases huj : b u = b j
      · have hjv : b j ≠ b v := fun h => huv (huj.trans h)
        simp only [blockDiagonalPart, if_neg hjv, mul_zero]
      · rw [ih u j huj, zero_mul]

lemma blockDiagonalPart_word_diagonal {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (M : Set (Square d)) (w : List (Square d)) (hw : WordIn M w) :
    blockMatrix b i (matrixProduct (w.map (blockDiagonalPart b))) =
      matrixProduct (w.map (blockMatrix b i)) := by
  have hupper : ∀ A ∈ (blockDiagonalPart b) '' M, IsUpperBlockTriangular b A := by
    rintro A ⟨B, _, rfl⟩
    exact blockDiagonalPart_upper b B
  calc
    blockMatrix b i (matrixProduct (w.map (blockDiagonalPart b))) =
        matrixProduct ((w.map (blockDiagonalPart b)).map (blockMatrix b i)) :=
      blockMatrix_matrixProduct b i ((blockDiagonalPart b) '' M) hupper
        (w.map (blockDiagonalPart b)) (word_image_in M (blockDiagonalPart b) w hw)
    _ = matrixProduct (w.map (blockMatrix b i)) := by
      simp only [List.map_map, Function.comp_def, blockMatrix_blockDiagonalPart]

lemma spectralNorm_blockDiagonal_le {d r : ℕ} (b : Fin d → Fin r) (A : Square d)
    (hA : ∀ u v, b u ≠ b v → A u v = 0) (c : ℝ) (hc : 0 ≤ c)
    (hdiag : ∀ i, spectralNorm (blockMatrix b i A) ≤ c) :
    spectralNorm A ≤ (d : ℝ) * c := by
  apply spectralNorm_le_card_mul_entry_bound A c hc
  intro u v
  by_cases huv : b u = b v
  · obtain ⟨iu, hiu⟩ := blockCoordinate_covers b (b u) u rfl
    obtain ⟨iv, hiv⟩ := blockCoordinate_covers b (b u) v huv.symm
    have hentry := spectralNorm_entry_bound (blockMatrix b (b u) A) iu iv
    change ‖A (blockCoordinate b (b u) iu) (blockCoordinate b (b u) iv)‖ ≤
      spectralNorm (blockMatrix b (b u) A) at hentry
    rw [hiu, hiv] at hentry
    exact hentry.trans (hdiag (b u))
  · rw [hA u v huv, norm_zero]
    exact hc

/-- A common word envelope for the exact block-diagonal parts. The factor is
fixed before the word and its length, and every diagonal radius may be zero. -/
lemma blockDiagonal_exponential_envelope {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (a : ℝ) (ha : 0 < a)
    (hradius : ∀ i, jointSpectralRadius (diagonalFamily b i M) < a) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ w : List (Square d), WordIn M w →
      spectralNorm (matrixProduct (w.map (blockDiagonalPart b))) ≤ K * a ^ w.length := by
  classical
  have hex : ∀ i : Fin r, ∃ K : ℝ, 1 ≤ K ∧
      ∀ n, familyGrowth (diagonalFamily b i M) n ≤ K * a ^ n := by
    intro i
    obtain ⟨_, K, hK, hbound⟩ := general_exponential_envelope
      (blockDim_pos_of_surjective b hb i) (diagonalFamily b i M)
      (diagonalFamily_isCompact b i M hM) (diagonalFamily_nonempty b i M hneM)
      a (hradius i)
    exact ⟨K, hK, hbound⟩
  choose K hK hbound using hex
  let S : ℝ := 1 + ∑ i : Fin r, K i
  have hS : 1 ≤ S := by
    have hs : 0 ≤ ∑ i : Fin r, K i :=
      Finset.sum_nonneg fun i _ => zero_le_one.trans (hK i)
    dsimp only [S]
    linarith only [hs]
  have hKS (i : Fin r) : K i ≤ S := by
    have hs := Finset.single_le_sum (fun j _ => zero_le_one.trans (hK j)) (Finset.mem_univ i)
    dsimp only [S]
    linarith only [hs]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨(d : ℝ) * S, one_le_mul_of_one_le_of_one_le hdR hS, ?_⟩
  intro w hw
  have hdiagonal (i : Fin r) :
      spectralNorm (blockMatrix b i (matrixProduct (w.map (blockDiagonalPart b)))) ≤
        S * a ^ w.length := by
    rw [blockDiagonalPart_word_diagonal b i M w hw]
    calc
      spectralNorm (matrixProduct (w.map (blockMatrix b i))) ≤
          familyGrowth (diagonalFamily b i M) w.length :=
        word_le_familyGrowth (diagonalFamily b i M) (diagonalFamily_isCompact b i M hM)
          w.length (w.map (blockMatrix b i)) (by simp only [List.length_map])
          (word_image_in M (blockMatrix b i) w hw)
      _ ≤ K i * a ^ w.length := hbound i w.length
      _ ≤ S * a ^ w.length := mul_le_mul_of_nonneg_right (hKS i) (pow_nonneg ha.le _)
  calc
    spectralNorm (matrixProduct (w.map (blockDiagonalPart b))) ≤
        (d : ℝ) * (S * a ^ w.length) :=
      spectralNorm_blockDiagonal_le b _ (blockDiagonalPart_product_support b w)
        (S * a ^ w.length) (mul_nonneg (zero_le_one.trans hS) (pow_nonneg ha.le _)) hdiagonal
    _ = ((d : ℝ) * S) * a ^ w.length := (mul_assoc _ _ _).symm

#print axioms blockDiagonal_exponential_envelope
#assert_trust kernel blockDiagonal_exponential_envelope

end NLA.MF06

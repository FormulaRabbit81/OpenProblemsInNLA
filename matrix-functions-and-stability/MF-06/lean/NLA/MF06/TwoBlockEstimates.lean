/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Entry estimates connect the exact two-block word expansion with the scalar
transition-sum theorem. Rectangular blocks require only finite sums; every
square-matrix norm below is the actual Euclidean operator norm. Dimension
constants are independent of word length, and no division by a word norm occurs.
-/
import NLA.MF06.TwoBlockWords
import NLA.MF06.TransitionWeights

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma rectangular_sandwich_entry_bound {m n : ℕ} (P : Square m)
    (D : Matrix (Fin m) (Fin n) ℂ) (Q : Square n) (L : ℝ) (hL : 0 ≤ L)
    (hD : ∀ i j, ‖D i j‖ ≤ L) (u : Fin m) (v : Fin n) :
    ‖(P * D * Q) u v‖ ≤
      ((m : ℝ) * (n : ℝ) * L) * (spectralNorm P * spectralNorm Q) := by
  have hPD (i : Fin m) (j : Fin n) :
      ‖(P * D) i j‖ ≤ (m : ℝ) * (spectralNorm P * L) := by
    rw [Matrix.mul_apply]
    calc
      ‖∑ k : Fin m, P i k * D k j‖ ≤ ∑ k : Fin m, ‖P i k * D k j‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin m, spectralNorm P * L := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        exact mul_le_mul (spectralNorm_entry_bound P i k) (hD k j)
          (norm_nonneg _) (spectralNorm_nonneg P)
      _ = (m : ℝ) * (spectralNorm P * L) := by simp
  rw [Matrix.mul_apply]
  calc
    ‖∑ k : Fin n, (P * D) u k * Q k v‖ ≤
        ∑ k : Fin n, ‖(P * D) u k * Q k v‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, ((m : ℝ) * (spectralNorm P * L)) * spectralNorm Q := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hPD u k) (spectralNorm_entry_bound Q k v) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (spectralNorm_nonneg P) hL))
    _ = ((m : ℝ) * (n : ℝ) * L) * (spectralNorm P * spectralNorm Q) := by simp; ring

lemma offDiagonalSum_entry_bound {d m n : ℕ} (M : Set (Square d))
    (f : Square d → Square m) (g : Square d → Square n)
    (h : Square d → Matrix (Fin m) (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hh : ∀ A ∈ M, ∀ u v, ‖h A u v‖ ≤ L)
    (w : List (Square d)) (hw : WordIn M w) (u : Fin m) (v : Fin n) :
    ‖offDiagonalSum f g h w u v‖ ≤
      ((m : ℝ) * (n : ℝ) * L) * ∑ i : Fin w.length, transitionWeight f g w i.val := by
  unfold offDiagonalSum
  rw [Matrix.sum_apply]
  calc
    ‖∑ i : Fin w.length,
        (matrixProduct ((w.drop (i.val + 1)).map f) * h (w.get i) *
          matrixProduct ((w.take i.val).map g)) u v‖ ≤
        ∑ i : Fin w.length,
          ‖(matrixProduct ((w.drop (i.val + 1)).map f) * h (w.get i) *
            matrixProduct ((w.take i.val).map g)) u v‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin w.length, ((m : ℝ) * (n : ℝ) * L) * transitionWeight f g w i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact rectangular_sandwich_entry_bound _ _ _ L hL
        (hh (w.get i) (hw _ (List.get_mem w i))) u v
    _ = ((m : ℝ) * (n : ℝ) * L) * ∑ i : Fin w.length, transitionWeight f g w i.val :=
      (Finset.mul_sum _ _ _).symm

lemma spectralNorm_twoBlock_le {m n : ℕ} (B : Square m)
    (D : Matrix (Fin m) (Fin n) ℂ) (C : Square n) (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hB : spectralNorm B ≤ K) (hC : spectralNorm C ≤ K)
    (hD : ∀ i j, ‖D i j‖ ≤ L) :
    spectralNorm (twoBlockMatrix B D C) ≤ ((m + n : ℕ) : ℝ) * (K + L) := by
  apply spectralNorm_le_card_mul_entry_bound _ _ (add_nonneg hK hL)
  intro u v
  change ‖Matrix.fromBlocks B D 0 C
    ((finSumFinEquiv (m := m) (n := n)).symm u)
    ((finSumFinEquiv (m := m) (n := n)).symm v)‖ ≤ K + L
  cases (finSumFinEquiv (m := m) (n := n)).symm u with
  | inl i =>
      cases (finSumFinEquiv (m := m) (n := n)).symm v with
      | inl j => exact (spectralNorm_entry_bound B i j).trans (hB.trans (le_add_of_nonneg_right hL))
      | inr j => exact (hD i j).trans (le_add_of_nonneg_left hK)
  | inr i =>
      cases (finSumFinEquiv (m := m) (n := n)).symm v with
      | inl j => simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero] using add_nonneg hK hL
      | inr j => exact (spectralNorm_entry_bound C i j).trans (hC.trans (le_add_of_nonneg_right hL))

/-- A single constant bounds every actual two-block word. The paired decay
controls the finite transition sum, including the empty word case. -/
lemma twoBlock_word_bound {d m n : ℕ} (M : Set (Square d))
    (f : Square d → Square m) (g : Square d → Square n)
    (h : Square d → Matrix (Fin m) (Fin n) ℂ) (K F q L : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hq : 0 < q) (hq1 : q < 1) (hL : 0 ≤ L)
    (hf : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map f)) ≤ K)
    (hg : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map g)) ≤ K)
    (hpair : ∀ w, WordIn M w →
      spectralNorm (matrixProduct (w.map f)) * spectralNorm (matrixProduct (w.map g)) ≤
        F * q ^ w.length)
    (hh : ∀ A ∈ M, ∀ u v, ‖h A u v‖ ≤ L)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct (w.map (fun A => twoBlockMatrix (f A) (h A) (g A)))) ≤
      ((m + n : ℕ) : ℝ) * (K + ((m : ℝ) * (n : ℝ) * L) *
        (2 * K ^ 2 + 4 * (((K ^ 4 * F / q) * q) / (1 - q) ^ 2) + 1)) := by
  let S : ℝ := 2 * K ^ 2 + 4 * (((K ^ 4 * F / q) * q) / (1 - q) ^ 2) + 1
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  rw [twoBlock_matrixProduct]
  apply spectralNorm_twoBlock_le _ _ _ K (((m : ℝ) * (n : ℝ) * L) * S) hK
    (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hL) hS)
    (hf w hw) (hg w hw)
  intro u v
  exact (offDiagonalSum_entry_bound M f g h L hL hh w hw u v).trans
    (mul_le_mul_of_nonneg_left (transition_sum_bound M f g K F q hK hF hq hq1 hf hg hpair w hw)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hL))

#print axioms twoBlock_word_bound
#assert_trust kernel twoBlock_word_bound

end NLA.MF06

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The tensor is the literal reindexed Kronecker matrix. Existing Mathlib algebra
and entrywise operator estimates suffice, with no tensor Hilbert-space machinery.
The two-sided norm comparison retains zero factors and uses no norm division.
-/
import NLA.MF06.Definitions
import NLA.MF07.BlockComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

theorem tensor_algebra {m n : ℕ} (A C : Square m) (B D : Square n) :
    tensorMatrix (1 : Square m) (1 : Square n) = 1 ∧
    tensorMatrix (A * C) (B * D) = tensorMatrix A B * tensorMatrix C D := by
  constructor
  · unfold tensorMatrix Matrix.kronecker
    rw [Matrix.one_kronecker_one]
    exact Matrix.submatrix_one _ (finProdFinEquiv (m := m) (n := n)).symm.injective
  · unfold tensorMatrix Matrix.kronecker
    rw [Matrix.mul_kronecker_mul]
    exact Matrix.submatrix_mul _ _ _ _ _ (finProdFinEquiv (m := m) (n := n)).symm.bijective

lemma exists_norm_max_entry {d : ℕ} (hd : 1 ≤ d) (A : Square d) :
    ∃ i j : Fin d, ∀ u v, ‖A u v‖ ≤ ‖A i j‖ := by
  obtain ⟨ij, _, hij⟩ := Finset.exists_max_image Finset.univ
    (fun ij : Fin d × Fin d => ‖A ij.1 ij.2‖)
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  exact ⟨ij.1, ij.2, fun u v => hij (u, v) (Finset.mem_univ _)⟩

theorem tensor_norm_comparison {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Square m) (B : Square n) :
    spectralNorm (tensorMatrix A B) ≤
      (m : ℝ) * (n : ℝ) * spectralNorm A * spectralNorm B ∧
    spectralNorm A * spectralNorm B ≤
      (m : ℝ) * (n : ℝ) * spectralNorm (tensorMatrix A B) := by
  constructor
  · have hentry (u v : Fin (m * n)) :
        ‖tensorMatrix A B u v‖ ≤ spectralNorm A * spectralNorm B := by
      -- Expand the literal Kronecker entry in the frozen finite-product
      -- coordinate order; both row and column use finProdFinEquiv.symm.
      change ‖A ((finProdFinEquiv (m := m) (n := n)).symm u).1
          ((finProdFinEquiv (m := m) (n := n)).symm v).1 *
        B ((finProdFinEquiv (m := m) (n := n)).symm u).2
          ((finProdFinEquiv (m := m) (n := n)).symm v).2‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (spectralNorm_entry_bound A _ _)
        (spectralNorm_entry_bound B _ _) (norm_nonneg _) (spectralNorm_nonneg A)
    have h := spectralNorm_le_card_mul_entry_bound (tensorMatrix A B) _
      (mul_nonneg (spectralNorm_nonneg A) (spectralNorm_nonneg B)) hentry
    simpa only [Nat.cast_mul, mul_assoc] using h
  · obtain ⟨i, j, hA⟩ := exists_norm_max_entry hm A
    obtain ⟨u, v, hB⟩ := exists_norm_max_entry hn B
    have hAn := spectralNorm_le_card_mul_entry_bound A _ (norm_nonneg _) hA
    have hBn := spectralNorm_le_card_mul_entry_bound B _ (norm_nonneg _) hB
    have hentry := spectralNorm_entry_bound (tensorMatrix A B)
      (finProdFinEquiv (i, u)) (finProdFinEquiv (j, v))
    have he : ‖A i j‖ * ‖B u v‖ ≤ spectralNorm (tensorMatrix A B) := by
      simpa only [tensorMatrix, Matrix.kronecker, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
        Equiv.symm_apply_apply, norm_mul] using hentry
    calc
      spectralNorm A * spectralNorm B ≤ ((m : ℝ) * ‖A i j‖) * ((n : ℝ) * ‖B u v‖) :=
        mul_le_mul hAn hBn (spectralNorm_nonneg B)
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ = ((m : ℝ) * (n : ℝ)) * (‖A i j‖ * ‖B u v‖) := by ring
      _ ≤ ((m : ℝ) * (n : ℝ)) * spectralNorm (tensorMatrix A B) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

#print axioms tensor_algebra
#assert_trust kernel tensor_algebra
#print axioms tensor_norm_comparison
#assert_trust kernel tensor_norm_comparison

end NLA.MF06

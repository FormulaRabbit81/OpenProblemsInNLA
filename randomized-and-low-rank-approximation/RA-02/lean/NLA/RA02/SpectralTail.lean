/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Actual filtered sums of decreasing Hermitian eigenvalues, including empty
dimension, full rank, and the singleton last-eigenvalue tail.
-/
import NLA.RA02.OrderedSpectrum
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma orderedEigenvalues_nonneg {n : ℕ} (A : Square n) (hA : A.PosSemidef)
    (i : Fin n) : 0 ≤ orderedEigenvalues A hA.isHermitian i := by
  rw [orderedEigenvalues_eq_reindexed A hA.isHermitian i]
  exact hA.eigenvalues_nonneg _

lemma orderedEigenvalues_pos {n : ℕ} (A : Square n) (hA : A.PosDef)
    (hH : A.IsHermitian) (i : Fin n) : 0 < orderedEigenvalues A hH i := by
  rw [orderedEigenvalues_eq_reindexed A hH i]
  exact hA.eigenvalues_pos _

lemma rankTail_nonneg {n : ℕ} (A : Square n) (hA : A.PosSemidef) (r : ℕ) :
    0 ≤ rankTail A hA.isHermitian r := by
  unfold rankTail
  exact Finset.sum_nonneg (fun i _ => orderedEigenvalues_nonneg A hA i)

lemma rankTail_full_rank {n : ℕ} (A : Square n) (hA : A.IsHermitian) :
    rankTail A hA n = 0 := by
  have hf : (Finset.univ.filter fun i : Fin n => n ≤ i.val) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact (Nat.not_le.mpr i.isLt) (Finset.mem_filter.mp hi).2
  simp only [rankTail, hf, Finset.sum_empty]

lemma rankTail_last (m : ℕ) (A : Square (m + 1)) (hA : A.IsHermitian) :
    rankTail A hA m = orderedEigenvalues A hA (Fin.last m) := by
  have hf : (Finset.univ.filter fun i : Fin (m + 1) => m ≤ i.val) = {Fin.last m} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      apply Fin.ext
      change i.val = m
      have hiLt := i.isLt
      omega
    · intro hi
      subst i
      exact le_rfl
  simp only [rankTail, hf, Finset.sum_singleton]

theorem spectral_tail_semantics (n : ℕ) (A : Square n) (hA : A.PosSemidef) :
    (∀ r : ℕ, 0 ≤ rankTail A hA.isHermitian r) ∧
    rankTail A hA.isHermitian n = 0 ∧
    ∀ (m : ℕ) (B : Square (m + 1)) (hB : B.IsHermitian),
      rankTail B hB m = orderedEigenvalues B hB (Fin.last m) := by
  exact ⟨rankTail_nonneg A hA, rankTail_full_rank A hA.isHermitian, rankTail_last⟩

#print axioms spectral_tail_semantics
#assert_trust kernel spectral_tail_semantics

end
end NLA.RA02

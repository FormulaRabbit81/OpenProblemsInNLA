/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Transport the genuinely decreasing spectrum, keeping Mathlib's arbitrary
matrix-index reordering separate from its order-preserving Fin cast.
-/
import NLA.RA02.EuclideanBridge
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Order.Fin.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

/-- The explicit permutation relating ordered indices to matrix eigenbasis indices. -/
def eigenvalueReindex (n : ℕ) : Fin n ≃ Fin n :=
  (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))

lemma orderedEigenvalues_eq_reindexed {n : ℕ} (A : Square n) (hA : A.IsHermitian)
    (i : Fin n) :
    orderedEigenvalues A hA i = hA.eigenvalues (eigenvalueReindex n i) := by
  simp [orderedEigenvalues, Matrix.IsHermitian.eigenvalues, eigenvalueReindex]

lemma orderedEigenvalues_antitone {n : ℕ} (A : Square n) (hA : A.IsHermitian) :
    Antitone (orderedEigenvalues A hA) := by
  intro i j hij
  exact hA.eigenvalues₀_antitone
    ((Fin.castOrderIso (Fintype.card_fin n).symm).monotone hij)

lemma orderedEigenvalues_eigenvector {n : ℕ} (A : Square n) (hA : A.IsHermitian)
    (i : Fin n) : ∃ x : Fin n → ℂ, x ≠ 0 ∧
      A *ᵥ x = (orderedEigenvalues A hA i : ℂ) • x := by
  let j := eigenvalueReindex n i
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis j), ?_, ?_⟩
  · intro hx
    exact hA.eigenvectorBasis.orthonormal.ne_zero j ((WithLp.ofLp_eq_zero 2).mp hx)
  · rw [orderedEigenvalues_eq_reindexed A hA i]
    simpa only [j, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hA.mulVec_eigenvectorBasis j

lemma trace_eq_sum_ordered {n : ℕ} (A : Square n) (hA : A.IsHermitian) :
    realTrace A = ∑ i : Fin n, orderedEigenvalues A hA i := by
  calc
    realTrace A = ∑ i : Fin n, hA.eigenvalues i := by
      change RCLike.re (K := ℂ) A.trace = ∑ i : Fin n, hA.eigenvalues i
      simpa only [map_sum, RCLike.ofReal_re] using
        congrArg (RCLike.re (K := ℂ)) hA.trace_eq_sum_eigenvalues
    _ = ∑ i : Fin n, hA.eigenvalues (eigenvalueReindex n i) :=
      ((eigenvalueReindex n).sum_comp hA.eigenvalues).symm
    _ = ∑ i : Fin n, orderedEigenvalues A hA i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (orderedEigenvalues_eq_reindexed A hA i).symm

theorem ordered_spectrum (n : ℕ) (A : Square n) (hA : A.IsHermitian) :
    Antitone (orderedEigenvalues A hA) ∧
    (∀ i : Fin n, ∃ x : Fin n → ℂ, x ≠ 0 ∧
      A *ᵥ x = (orderedEigenvalues A hA i : ℂ) • x) ∧
    realTrace A = ∑ i : Fin n, orderedEigenvalues A hA i := by
  exact ⟨orderedEigenvalues_antitone A hA, orderedEigenvalues_eigenvector A hA,
    trace_eq_sum_ordered A hA⟩

#print axioms ordered_spectrum
#assert_trust kernel ordered_spectrum

end
end NLA.RA02

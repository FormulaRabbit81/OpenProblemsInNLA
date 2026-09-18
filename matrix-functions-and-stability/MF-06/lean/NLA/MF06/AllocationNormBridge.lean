/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

For each original block, max/min allocations only reorder the two compound
factors. We reorder the actual entry coordinates before applying any norm
inequality. No determinant, entry, or norm is divided out: zero factors and
singular matrices are included. The fixed dimension factor lies outside all
word-length exponents used later.
-/
import NLA.MF06.AllocationDimensions
import NLA.MF06.TensorAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma allocationCoordinate_encode {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (u : AllocationIndex b a) :
    allocationCoordinate b a (Fintype.equivFin (AllocationIndex b a) u) = u :=
  (Fintype.equivFin (AllocationIndex b a)).symm_apply_apply u

/-- Each product of two allocation entries is literally a product of a max
allocation entry and a min allocation entry. The selected coordinates may be
swapped independently in each original block, for both rows and columns. -/
lemma allocation_pair_entry_factorization {d r : ℕ} (b : Fin d → Fin r)
    (a c : Allocation b) (P : Square d)
    (u v : Fin (allocationDim b a)) (s t : Fin (allocationDim b c)) :
    ∃ U V : Fin (allocationDim b (allocationMax a c)),
      ∃ S T : Fin (allocationDim b (allocationMin a c)),
        allocationMatrix b a P u v * allocationMatrix b c P s t =
          allocationMatrix b (allocationMax a c) P U V *
            allocationMatrix b (allocationMin a c) P S T := by
  classical
  have hlocal (i : Fin r) :
      ∃ U V : Fin (compoundDim (blockDim b i) ((allocationMax a c) i).val),
        ∃ S T : Fin (compoundDim (blockDim b i) ((allocationMin a c) i).val),
          compoundMatrix (a i).val (blockMatrix b i P)
              (allocationCoordinate b a u i) (allocationCoordinate b a v i) *
            compoundMatrix (c i).val (blockMatrix b i P)
              (allocationCoordinate b c s i) (allocationCoordinate b c t i) =
            compoundMatrix ((allocationMax a c) i).val (blockMatrix b i P) U V *
              compoundMatrix ((allocationMin a c) i).val (blockMatrix b i P) S T := by
    rcases le_total (a i) (c i) with h | h
    · dsimp only [allocationMax, allocationMin]
      rw [max_eq_right h, min_eq_left h]
      exact ⟨allocationCoordinate b c s i, allocationCoordinate b c t i,
        allocationCoordinate b a u i, allocationCoordinate b a v i, mul_comm _ _⟩
    · dsimp only [allocationMax, allocationMin]
      rw [max_eq_left h, min_eq_right h]
      exact ⟨allocationCoordinate b a u i, allocationCoordinate b a v i,
        allocationCoordinate b c s i, allocationCoordinate b c t i, rfl⟩
  choose U V S T hfactor using hlocal
  refine ⟨Fintype.equivFin (AllocationIndex b (allocationMax a c)) U,
    Fintype.equivFin (AllocationIndex b (allocationMax a c)) V,
    Fintype.equivFin (AllocationIndex b (allocationMin a c)) S,
    Fintype.equivFin (AllocationIndex b (allocationMin a c)) T, ?_⟩
  simp only [allocationMatrix, allocationCoordinate_encode]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => hfactor i)

/-- C29. A word-independent dimension factor suffices; the exact frozen
statement allows every original matrix, including all singular cases. -/
theorem allocation_tensor_norm_bridge {d r : ℕ} (b : Fin d → Fin r)
    (a c : Allocation b) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : Square d,
      spectralNorm (tensorMatrix (allocationMatrix b a P) (allocationMatrix b c P)) ≤
        D * spectralNorm (allocationMatrix b (allocationMax a c) P) *
          spectralNorm (allocationMatrix b (allocationMin a c) P) := by
  have hdim : 0 < allocationDim b a * allocationDim b c :=
    Nat.mul_pos (Nat.zero_lt_one.trans_le (allocation_dimensions b a).2.2)
      (Nat.zero_lt_one.trans_le (allocation_dimensions b c).2.2)
  refine ⟨((allocationDim b a * allocationDim b c : ℕ) : ℝ), by exact_mod_cast hdim, ?_⟩
  intro P
  have hentry (u v : Fin (allocationDim b a * allocationDim b c)) :
      ‖tensorMatrix (allocationMatrix b a P) (allocationMatrix b c P) u v‖ ≤
        spectralNorm (allocationMatrix b (allocationMax a c) P) *
          spectralNorm (allocationMatrix b (allocationMin a c) P) := by
    obtain ⟨U, V, S, T, he⟩ := allocation_pair_entry_factorization b a c P
      ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm u).1
      ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm v).1
      ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm u).2
      ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm v).2
    change ‖allocationMatrix b a P
        ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm u).1
        ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm v).1 *
      allocationMatrix b c P
        ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm u).2
        ((finProdFinEquiv (m := allocationDim b a) (n := allocationDim b c)).symm v).2‖ ≤ _
    rw [he, norm_mul]
    exact mul_le_mul (spectralNorm_entry_bound _ U V) (spectralNorm_entry_bound _ S T)
      (norm_nonneg _) (spectralNorm_nonneg _)
  have hbound := spectralNorm_le_card_mul_entry_bound
    (tensorMatrix (allocationMatrix b a P) (allocationMatrix b c P)) _
    (mul_nonneg (spectralNorm_nonneg _) (spectralNorm_nonneg _)) hentry
  simpa only [mul_assoc] using hbound

#print axioms allocation_pair_entry_factorization
#assert_trust kernel allocation_pair_entry_factorization
#print axioms allocation_tensor_norm_bridge
#assert_trust kernel allocation_tensor_norm_bridge

end NLA.MF06

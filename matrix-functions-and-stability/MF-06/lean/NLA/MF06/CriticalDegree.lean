/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The actual degree-one compound makes the finite critical-degree set nonempty.
Its greatest element has a strict gap at every higher degree, using the
proved radius-power bound. No product-boundedness premise is added.
-/
import NLA.MF06.CompoundFirstDegree

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma exists_maximal_critical_degree {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hradius : jointSpectralRadius M = 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧
      jointSpectralRadius (compoundFamily k M) = 1 ∧
      ∀ j : ℕ, k < j → j ≤ d → jointSpectralRadius (compoundFamily j M) < 1 := by
  classical
  let s := (Finset.range (d + 1)).filter
    (fun k => 1 ≤ k ∧ jointSpectralRadius (compoundFamily k M) = 1)
  have hmem (k : ℕ) : k ∈ s ↔
      k ≤ d ∧ 1 ≤ k ∧ jointSpectralRadius (compoundFamily k M) = 1 := by
    simp only [s, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hone : 1 ∈ s := (hmem 1).mpr ⟨hd, le_rfl,
    (compound_family_semantics hd M hM hneM).2.trans hradius⟩
  have hs : s.Nonempty := ⟨1, hone⟩
  let k := s.max' hs
  have hk := (hmem k).mp (Finset.max'_mem s hs)
  refine ⟨k, hk.2.1, hk.1, hk.2.2, ?_⟩
  intro j hkj hjd
  have hle : jointSpectralRadius (compoundFamily j M) ≤ 1 := by
    have h := (compound_family_semantics hd M hM hneM).1 j hjd
    simpa only [hradius, one_pow] using h.2.2
  apply lt_of_le_of_ne hle
  intro heq
  have hjmem := (hmem j).mpr ⟨hjd, by omega, heq⟩
  have hjk : j ≤ k := Finset.le_max' s j hjmem
  exact (not_le_of_gt hkj) hjk

#print axioms exists_maximal_critical_degree
#assert_trust kernel exists_maximal_critical_degree

end NLA.MF06

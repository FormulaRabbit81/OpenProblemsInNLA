/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A genuine irreducible flag bounds the diagonal families. The maximal critical
degree then has bounded allocation blocks and strict gaps between distinct
paired blocks. The actual exterior representation and inverse similarity
give boundedness of the original critical compound family.
-/
import NLA.MF06.CriticalDegree
import NLA.MF06.IrreducibleFlag
import NLA.MF06.IrreducibleSubcritical
import NLA.MF06.CompoundSimilarity
import NLA.MF06.CriticalAllocationGap
import NLA.MF06.CompoundNonresonance

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

theorem critical_compound_product_bounded {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hradius : jointSpectralRadius M = 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧
      jointSpectralRadius (compoundFamily k M) = 1 ∧
      IsProductBounded (compoundFamily k M) ∧
      ∀ j : ℕ, k < j → j ≤ d → jointSpectralRadius (compoundFamily j M) < 1 := by
  obtain ⟨k, hk0, hkd, hcritical, hhigher⟩ := exists_maximal_critical_degree hd M hM hneM hradius
  obtain ⟨r, _hr, _hrd, b, hb, Q, R, hQR, hRQ, hupper, hirr⟩ := irreducible_flag hd M
  let G := conjugateFamily Q R M
  obtain ⟨hG, hneG, hGradius, _⟩ := similarity_semantics hd Q R hQR hRQ M hM hneM
  have hGone : jointSpectralRadius G = 1 := hGradius.trans hradius
  have hdiag : ∀ i : Fin r, IsProductBounded (diagonalFamily b i G) := by
    intro i
    apply irreducible_radius_le_one_product_bounded (blockDim_pos_of_surjective b hb i)
      (diagonalFamily b i G) (diagonalFamily_isCompact b i G hG)
      (diagonalFamily_nonempty b i G hneG) (hirr i)
    exact (diagonal_radius_le hd b hb i G hG hneG hupper).trans hGone.le
  have hhigherG (j : ℕ) (hkj : k < j) (hjd : j ≤ d) :
      jointSpectralRadius (compoundFamily j G) < 1 := by
    rw [(compound_similarity_semantics hd Q R hQR hRQ M hM hneM j hjd).1]
    exact hhigher j hkj hjd
  have hcompoundG : IsProductBounded (compoundFamily k G) := by
    apply compound_nonresonance_product_bounded hd b hb G hG hneG hupper k hkd
    · intro a
      exact allocation_product_bounded hd b G hG hneG hdiag a.val
    · intro a c hne
      exact critical_allocation_nonresonance hd b hb G hG hneG hupper hdiag
        k hk0 hkd hhigherG a c hne
  exact ⟨k, hk0, hkd, hcritical,
    (compound_similarity_semantics hd Q R hQR hRQ M hM hneM k hkd).2.mp hcompoundG,
    hhigher⟩

#print axioms critical_compound_product_bounded
#assert_trust kernel critical_compound_product_bounded

end NLA.MF06

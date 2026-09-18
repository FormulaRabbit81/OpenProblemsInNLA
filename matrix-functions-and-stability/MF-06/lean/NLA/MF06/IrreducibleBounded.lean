/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The argument proves the irreducible product-boundedness prerequisite directly;
it does not import an unproved extremal or Barabanov norm assertion.

A product whose norm exceeds the reciprocal bridge constant would amplify
every vector after a bounded-length legal bridge. The actual radius-one
exponential envelope excludes this. Thus a single fixed constant bounds every
word length, including the empty word.
-/
import NLA.MF06.IrreducibleBridge
import NLA.MF06.WordAmplification

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

/-- C14. Product boundedness is a conclusion of genuine irreducibility. -/
theorem irreducible_radius_one_product_bounded {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hirr : FamilyIrreducible M) (hradius : jointSpectralRadius M = 1) :
    IsProductBounded M := by
  obtain ⟨N, c, hc, hbridge⟩ := irreducible_bounded_bridge hd M hirr
  refine ⟨max 1 (2 / c), le_max_left _ _, ?_⟩
  intro n
  by_contra hnot
  obtain ⟨p, _, hp, he⟩ := familyGrowth_attained M hM hneM n
  have hlarge : 2 / c < spectralNorm (matrixProduct p) := by
    rw [he]
    exact (le_max_right 1 (2 / c)).trans_lt (lt_of_not_ge hnot)
  have hγ : 1 < c * spectralNorm (matrixProduct p) := by
    have htwo := (div_lt_iff₀ hc).mp hlarge
    nlinarith only [htwo]
  have hstep : ∀ x : EuclideanVector d, ∃ w : List (Square d), WordIn M w ∧
      w.length ≤ N + p.length ∧
        (c * spectralNorm (matrixProduct p)) * ‖x‖ ≤ ‖applyMatrix (matrixProduct w) x‖ := by
    intro x
    obtain ⟨w, hw, hwN, hgrowth⟩ := hbridge
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (matrixProduct p)) x
    refine ⟨w ++ p, (WordIn_append_iff M w p).mpr ⟨hw, hp⟩, ?_, ?_⟩
    · simpa only [List.length_append] using Nat.add_le_add_right hwN p.length
    · rw [matrixProduct_append, applyMatrix_mul]
      exact hgrowth
  exact bounded_word_amplification_contradiction hd M hM hneM hradius
    (N + p.length) (c * spectralNorm (matrixProduct p)) hγ hstep

#print axioms irreducible_radius_one_product_bounded
#assert_trust kernel irreducible_radius_one_product_bounded

end NLA.MF06

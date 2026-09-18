/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The reused arbitrary-radius envelope and root-limit results retain the MF05
mathematical attribution to Matthew J. Colbrook.

A fixed factor outside the word length preserves boundedness and the order
of actual joint spectral radii. Dimensions may differ. Zero radius is retained,
and no real roots are numerically evaluated.
-/
import NLA.MF06.Definitions
import NLA.MF05.RootLimit

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma product_bounded_of_growth_comparison {m n : ℕ}
    (M : Set (Square m)) (N : Set (Square n)) (D : ℝ) (hD : 1 ≤ D)
    (hcomparison : ∀ k : ℕ, familyGrowth N k ≤ D * familyGrowth M k)
    (hbounded : IsProductBounded M) : IsProductBounded N := by
  obtain ⟨K, hK, hbound⟩ := hbounded
  refine ⟨D * K, one_le_mul_of_one_le_of_one_le hD hK, ?_⟩
  intro k
  exact (hcomparison k).trans
    (mul_le_mul_of_nonneg_left (hbound k) (zero_le_one.trans hD))

lemma radius_le_of_growth_comparison {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Set (Square m)) (N : Set (Square n))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (D : ℝ) (hD : 1 ≤ D)
    (hcomparison : ∀ k : ℕ, familyGrowth N k ≤ D * familyGrowth M k) :
    jointSpectralRadius N ≤ jointSpectralRadius M := by
  by_contra hnot
  obtain ⟨a, hra, har⟩ := exists_between (lt_of_not_ge hnot)
  obtain ⟨ha, K, hK, hbound⟩ := general_exponential_envelope hm M hM hneM a hra
  have hupper : jointSpectralRadius N ≤ a := by
    apply exponential_bound_controls_radius hn N hN hneN (D * K) a
      (one_le_mul_of_one_le_of_one_le hD hK) ha
    intro k
    calc
      familyGrowth N k ≤ D * familyGrowth M k := hcomparison k
      _ ≤ D * (K * a ^ k) := mul_le_mul_of_nonneg_left (hbound k) (zero_le_one.trans hD)
      _ = (D * K) * a ^ k := (mul_assoc _ _ _).symm
  exact (not_le_of_gt har) hupper

#print axioms product_bounded_of_growth_comparison
#assert_trust kernel product_bounded_of_growth_comparison
#print axioms radius_le_of_growth_comparison
#assert_trust kernel radius_le_of_growth_comparison

end NLA.MF06

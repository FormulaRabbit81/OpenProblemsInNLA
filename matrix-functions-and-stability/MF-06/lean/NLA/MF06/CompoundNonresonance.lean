/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The actual compound allocation partition satisfies every hypothesis of the
proved finite-block nonresonance theorem. Actual-word comparisons transfer
allocation product bounds and strict paired radius bounds to its real
diagonal blocks. The finite allocation bijection preserves distinct pairs.
-/
import NLA.MF06.CompoundPairedWords
import NLA.MF06.BlockNonresonance

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

theorem compound_nonresonance_product_bounded {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) (k : ℕ) (hk : k ≤ d)
    (halloc : ∀ a : DegreeAllocation b k, IsProductBounded (allocationFamily b a.val M))
    (hpair : ∀ a c : DegreeAllocation b k, a ≠ c →
      jointSpectralRadius
        (pairedFamily M (allocationMatrix b a.val) (allocationMatrix b c.val)) < 1) :
    IsProductBounded (compoundFamily k M) := by
  apply block_nonresonance_product_bounded ((compound_dimensions d k).2 hk)
    (compoundAllocationLabel b k) (compoundAllocationLabel_surjective b k) (compoundFamily k M)
    (hM.image (continuous_compoundMatrix k)) (hneM.image _) (compoundFamily_upper b k M hupper)
  · intro t
    exact compoundDiagonal_product_bounded b k t M hM hneM hupper
      (halloc (allocationOrderEquiv b k t))
  · intro s t hst
    exact (compoundDiagonal_pair_radius_le b k s t M hM hneM hupper).trans_lt
      (hpair (allocationOrderEquiv b k s) (allocationOrderEquiv b k t)
        (fun h => hst ((allocationOrderEquiv b k).injective h)))

#print axioms compound_nonresonance_product_bounded
#assert_trust kernel compound_nonresonance_product_bounded

end NLA.MF06

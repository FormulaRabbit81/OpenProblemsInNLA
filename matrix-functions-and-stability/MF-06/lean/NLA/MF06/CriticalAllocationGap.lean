/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The componentwise max has strictly higher degree. Its actual allocation
radius is below the corresponding exterior radius, while boundedness of the
min allocation supplies the paired-word comparison. No independent choice
of generators in separate tensor factors is made.
-/
import NLA.MF06.AllocationPairRadius
import NLA.MF06.AllocationDimensions
import NLA.MF06.CompoundAllocationRadius

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

theorem critical_allocation_nonresonance {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (hdiag : ∀ i : Fin r, IsProductBounded (diagonalFamily b i M))
    (k : ℕ) (hk0 : 1 ≤ k) (hkd : k ≤ d)
    (hhigher : ∀ j : ℕ, k < j → j ≤ d → jointSpectralRadius (compoundFamily j M) < 1)
    (a c : DegreeAllocation b k) (hne : a ≠ c) :
    jointSpectralRadius
      (pairedFamily M (allocationMatrix b a.val) (allocationMatrix b c.val)) < 1 := by
  classical
  let amax := allocationMax a.val c.val
  let j := allocationDegree b amax
  have hjd : j ≤ d := (allocation_dimensions b amax).2.1
  have hkj : k < j := (distinct_allocation_degrees b k a c hne).1
  have hmin := allocation_product_bounded hd b M hM hneM hdiag (allocationMin a.val c.val)
  have hmax : jointSpectralRadius (allocationFamily b amax M) ≤
      jointSpectralRadius (compoundFamily j M) := by
    rw [compound_allocation_radius hd b hb M hM hneM hupper j hjd]
    exact le_csSup (Set.finite_range _).bddAbove ⟨⟨amax, rfl⟩, rfl⟩
  exact ((allocation_pair_radius_le_max b M hM hneM hupper a.val c.val hmin).trans hmax).trans_lt
    (hhigher j hkj hjd)

#print axioms critical_allocation_nonresonance
#assert_trust kernel critical_allocation_nonresonance

end NLA.MF06

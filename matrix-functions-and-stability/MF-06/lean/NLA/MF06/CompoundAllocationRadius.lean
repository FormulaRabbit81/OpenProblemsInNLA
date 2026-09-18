/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The actual compound matrix has the proved surjective occupation partition.
Its genuine diagonal-family radii equal the actual allocation-family radii by
same-word norm comparison. The established triangular radius formula and the
proved finite allocation enumeration yield exactly the frozen C27 supremum.
-/
import NLA.MF06.CompoundAllocationWords
import NLA.MF06.BlockRadius

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

theorem compound_allocation_radius {d r : ℕ} (hd : 1 ≤ d)
    (b : Fin d → Fin r) (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) (k : ℕ) (hk : k ≤ d) :
    jointSpectralRadius (compoundFamily k M) =
      sSup (Set.range (fun a : DegreeAllocation b k =>
        jointSpectralRadius (allocationFamily b a.val M))) := by
  have hrange :
      Set.range (fun t : Fin (Fintype.card (DegreeAllocation b k)) =>
        jointSpectralRadius (diagonalFamily (compoundAllocationLabel b k) t (compoundFamily k M))) =
      Set.range (fun a : DegreeAllocation b k => jointSpectralRadius (allocationFamily b a.val M)) := by
    calc
      _ = Set.range ((fun a : DegreeAllocation b k =>
          jointSpectralRadius (allocationFamily b a.val M)) ∘ allocationOrderEquiv b k) := by
        congr 1
        funext t
        exact compoundDiagonal_radius_eq b k t M hM hneM hupper
      _ = _ := (allocationOrderEquiv b k).surjective.range_comp _
  calc
    jointSpectralRadius (compoundFamily k M) =
        sSup (Set.range (fun t : Fin (Fintype.card (DegreeAllocation b k)) =>
          jointSpectralRadius (diagonalFamily (compoundAllocationLabel b k) t
            (compoundFamily k M)))) :=
      block_radius_formula ((compound_dimensions d k).2 hk) (compoundAllocationLabel b k)
        (compoundAllocationLabel_surjective b k) (compoundFamily k M)
        (hM.image (continuous_compoundMatrix k)) (hneM.image _)
        (compoundFamily_upper b k M hupper)
    _ = sSup (Set.range (fun a : DegreeAllocation b k =>
        jointSpectralRadius (allocationFamily b a.val M))) := congrArg sSup hrange

#print axioms compound_allocation_radius
#assert_trust kernel compound_allocation_radius

end NLA.MF06

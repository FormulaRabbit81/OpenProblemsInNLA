/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Reciprocal conjugation is counted with complete algebraic multiplicities.
The proof explicitly accounts for roots at zero and lost leading degree;
there is no generic nonsingularity or absence-of-unit-roots assumption.
-/
import NLA.MF18.ReflectedRoots
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem conjugate_zero_multiplicity (p : CPoly) :
    (p.map (starRingEnd ℂ)).rootMultiplicity 0 = p.rootMultiplicity 0 := by
  simpa only [map_zero] using
    (Polynomial.eq_rootMultiplicity_map (p := p) (f := starRingEnd ℂ) star_injective (0 : ℂ)).symm

theorem conjugate_disk_count (p : CPoly) :
    diskRootCount (p.map (starRingEnd ℂ)) = diskRootCount p := by
  classical
  have hr := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := p) (f := starRingEnd ℂ) star_injective (IsAlgClosed.card_roots_eq_natDegree (p := p))
  unfold diskRootCount
  rw [← hr, Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro z _
  simp only [Function.comp_apply, starRingEnd_apply, norm_star]

theorem norm_partition_card (s : Multiset ℂ) :
    (s.filter (fun z => ‖z‖ < 1)).card + (s.filter (fun z => ‖z‖ = 1)).card +
      (s.filter (fun z => 1 < ‖z‖)).card = s.card := by
  classical
  have hsplit := congrArg Multiset.card
    (Multiset.filter_add_not (fun z : ℂ => ‖z‖ < 1) s)
  have hrest := congrArg Multiset.card
    (Multiset.filter_add_not (fun z : ℂ => ‖z‖ = 1)
      (s.filter (fun z : ℂ => ¬‖z‖ < 1)))
  have hequal : (s.filter (fun z : ℂ => ¬‖z‖ < 1)).filter (fun z => ‖z‖ = 1) =
      s.filter (fun z => ‖z‖ = 1) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z _
    exact ⟨And.left, fun h => ⟨h, not_lt_of_ge h.ge⟩⟩
  have hgreater : (s.filter (fun z : ℂ => ¬‖z‖ < 1)).filter (fun z => ¬‖z‖ = 1) =
      s.filter (fun z => 1 < ‖z‖) := by
    rw [Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z _
    constructor
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h.2) (Ne.symm h.1)
    · intro h
      exact ⟨ne_of_gt h, not_lt_of_ge h.le⟩
  rw [Multiset.card_add] at hsplit hrest
  rw [hequal, hgreater] at hrest
  omega

theorem reciprocal_count_identity {n : ℕ} (C R : Mat n)
    (hR : R.IsHermitian) (hreg : unregularizedPolynomial C R ≠ 0) :
    (unregularizedPolynomial C R).natDegree +
      (unregularizedPolynomial C R).rootMultiplicity 0 = 2 * n ∧
    2 * diskRootCount (unregularizedPolynomial C R) +
      circleRootCount (unregularizedPolynomial C R) = 2 * n := by
  have hd : (unregularizedPolynomial C R).natDegree ≤ 2 * n :=
    pencil_degree_bound C C.conjTranspose R
  have hc := reflected_zero_and_disk_count (2 * n) (unregularizedPolynomial C R) hreg hd
  rw [unregularized_reflection C R hR, conjugate_zero_multiplicity, conjugate_disk_count] at hc
  have hp := norm_partition_card (unregularizedPolynomial C R).roots
  rw [IsAlgClosed.card_roots_eq_natDegree] at hp
  -- Name the interior and circle filtered cardinalities by the frozen root-count definitions.
  change diskRootCount (unregularizedPolynomial C R) +
    circleRootCount (unregularizedPolynomial C R) +
    ((unregularizedPolynomial C R).roots.filter (fun z : ℂ => 1 < ‖z‖)).card =
    (unregularizedPolynomial C R).natDegree at hp
  constructor <;> omega

#print axioms reciprocal_count_identity

end NLA.MF18

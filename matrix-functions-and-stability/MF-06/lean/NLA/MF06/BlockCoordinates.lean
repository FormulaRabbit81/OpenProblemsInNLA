/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The frozen block coordinates enumerate the actual fibers of the given label.
The coordinate and summation facts below do not choose a different partition.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma blockCoordinate_label {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (j : Fin (blockDim b i)) : b (blockCoordinate b i j) = i :=
  ((Fintype.equivFin (BlockIndex b i)).symm j).property

lemma blockCoordinate_injective {d r : ℕ} (b : Fin d → Fin r) (i : Fin r) :
    Function.Injective (blockCoordinate b i) := by
  intro u v huv
  apply (Fintype.equivFin (BlockIndex b i)).symm.injective
  exact Subtype.ext huv

lemma blockCoordinate_covers {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (j : Fin d) (hj : b j = i) : ∃ u, blockCoordinate b i u = j := by
  refine ⟨Fintype.equivFin (BlockIndex b i) ⟨j, hj⟩, ?_⟩
  exact congrArg Subtype.val ((Fintype.equivFin (BlockIndex b i)).symm_apply_apply ⟨j, hj⟩)

lemma blockDim_pos_of_surjective {d r : ℕ} (b : Fin d → Fin r)
    (hb : Function.Surjective b) (i : Fin r) : 1 ≤ blockDim b i := by
  change 0 < Fintype.card (BlockIndex b i)
  apply Fintype.card_pos_iff.mpr
  obtain ⟨j, hj⟩ := hb i
  exact ⟨⟨j, hj⟩⟩

lemma blockDim_le {d r : ℕ} (b : Fin d → Fin r) (i : Fin r) : blockDim b i ≤ d := by
  simpa only [blockDim, Fintype.card_fin] using
    Fintype.card_le_of_injective (fun j : BlockIndex b i => j.val) Subtype.val_injective

/-- A supported ambient sum is precisely the sum over the frozen fiber
enumeration. The complementary fiber contributes literal zero. -/
lemma blockCoordinate_sum {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (f : Fin d → ℂ) (hf : ∀ j, b j ≠ i → f j = 0) :
    (∑ j : Fin d, f j) = ∑ j : Fin (blockDim b i), f (blockCoordinate b i j) := by
  classical
  have hz : (∑ j : {j : Fin d // ¬ b j = i}, f j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact hf j.val j.property
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun j : Fin d => b j = i) f
  rw [hz, add_zero] at hsum
  calc
    (∑ j : Fin d, f j) = ∑ j : BlockIndex b i, f j.val := hsum.symm
    _ = ∑ j : Fin (blockDim b i), f (blockCoordinate b i j) :=
      ((Fintype.equivFin (BlockIndex b i)).symm.sum_comp
        (fun j : BlockIndex b i => f j.val)).symm

lemma continuous_blockMatrix {d r : ℕ} (b : Fin d → Fin r) (i : Fin r) :
    Continuous (blockMatrix b i) := by
  change Continuous (fun A : Square d => fun u v =>
    A (blockCoordinate b i u) (blockCoordinate b i v))
  exact continuous_pi fun u => continuous_pi fun v =>
    (continuous_apply (blockCoordinate b i v)).comp
      (continuous_apply (blockCoordinate b i u))

lemma diagonalFamily_isCompact {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (M : Set (Square d)) (hM : IsCompact M) : IsCompact (diagonalFamily b i M) :=
  hM.image (continuous_blockMatrix b i)

lemma diagonalFamily_nonempty {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (M : Set (Square d)) (hneM : M.Nonempty) : (diagonalFamily b i M).Nonempty :=
  hneM.image _

#print axioms blockCoordinate_sum
#assert_trust kernel blockCoordinate_sum
#print axioms diagonalFamily_isCompact
#assert_trust kernel diagonalFamily_isCompact

end NLA.MF06

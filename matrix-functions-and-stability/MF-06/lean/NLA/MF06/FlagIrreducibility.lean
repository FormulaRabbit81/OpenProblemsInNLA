/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A diagonal invariant subspace lifts through the concrete block projection
to a common invariant subspace between successive flag prefixes. Saturation
then makes the diagonal subspace zero or the whole actual fiber space.
-/
import NLA.MF06.FlagQuotient

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma diagonal_irreducible_of_saturated_flag {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d)) (hmono : Monotone F)
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r)
    (hspan : ∀ i, Submodule.span ℂ (B '' {j | (b j).val < i.val}) = F i)
    (M : Set (Square d)) (hinv : ∀ i, FamilyInvariant M (F i))
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b (inBasis B A))
    (hsat : ∀ i : Fin r, ∀ T : Submodule ℂ (EuclideanVector d), FamilyInvariant M T →
      F i.castSucc ≤ T → T ≤ F i.succ → T = F i.castSucc ∨ T = F i.succ)
    (i : Fin r) : FamilyIrreducible (diagonalFamily b i (inBasis B '' M)) := by
  intro S hS
  let L := flagBlockProjection B b i
  let T : Submodule ℂ (EuclideanVector d) := F i.succ ⊓ S.comap L
  have hTinv : FamilyInvariant M T := by
    intro A hA x hx
    refine ⟨hinv i.succ A hA x hx.1, ?_⟩
    change flagBlockProjection B b i (applyMatrix A x) ∈ S
    rw [flagBlockProjection_action F B b hspan A (hupper A hA) i x hx.1]
    exact hS _ ⟨inBasis B A, ⟨A, hA, rfl⟩, rfl⟩ _ hx.2
  have hleft : F i.castSucc ≤ T := by
    intro x hx
    have hxnext : x ∈ F i.succ := hmono (le_of_lt i.castSucc_lt_succ) hx
    refine ⟨hxnext, ?_⟩
    change flagBlockProjection B b i x ∈ S
    rw [(flagBlockProjection_zero_iff F B b hspan i x hxnext).mpr hx]
    exact S.zero_mem
  have hright : T ≤ F i.succ := inf_le_left
  rcases hsat i T hTinv hleft hright with hT | hT
  · left
    apply le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨x, hx, hxz⟩ := flagBlockProjection_surjective_on F B b hspan i z
    have hxT : x ∈ T := ⟨hx, by change flagBlockProjection B b i x ∈ S; rwa [hxz]⟩
    have hxprev : x ∈ F i.castSucc := hT ▸ hxT
    have hzero := (flagBlockProjection_zero_iff F B b hspan i x hx).mpr hxprev
    change z = 0
    exact hxz.symm.trans hzero
  · right
    apply top_unique
    intro z _
    obtain ⟨x, hx, hxz⟩ := flagBlockProjection_surjective_on F B b hspan i z
    have hxT : x ∈ T := by rw [hT]; exact hx
    have hmem := hxT.2
    change flagBlockProjection B b i x ∈ S at hmem
    rwa [hxz] at hmem

#print axioms diagonal_irreducible_of_saturated_flag
#assert_trust kernel diagonal_irreducible_of_saturated_flag

end NLA.MF06

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The finite flag is spanned by subsets of one actual basis. This follows from
nested independent extensions inside the original subspaces. The terminal
set is a basis, reindexed only by the proved ambient dimension.
-/
import NLA.MF06.NestedIndependent

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma exists_basis_spanning_chain {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d))
    (hF : Monotone F) (h0 : F 0 = ⊥) (htop : F (Fin.last r) = ⊤) :
    ∃ B : Module.Basis (Fin d) ℂ (EuclideanVector d),
      ∀ i, Submodule.span ℂ (B '' {j | B j ∈ F i}) = F i := by
  classical
  let index (n : ℕ) : Fin (r + 1) := ⟨min n r, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hindex : Monotone index := by
    intro a b hab
    exact min_le_min_right r hab
  have hindex0 : index 0 = 0 := by ext; simp [index]
  have hindexr : index r = Fin.last r := by ext; simp [index]
  have hindexi (i : Fin (r + 1)) : index i.val = i := by
    ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  obtain ⟨S, hS0, hSmono, hS⟩ := exists_nested_independent_sets
    (fun n => F (index n)) (hF.comp hindex) (by rw [hindex0, h0])
  have hli : LinearIndependent ℂ ((↑) : S r → EuclideanVector d) :=
    (hS r).1.linearIndependent_restrict
  have hspan : Submodule.span ℂ (Set.range ((↑) : S r → EuclideanVector d)) = ⊤ := by
    rw [Subtype.range_coe, (hS r).2, hindexr, htop]
  let B0 : Module.Basis (S r) ℂ (EuclideanVector d) := Module.Basis.mk hli (le_of_eq hspan.symm)
  let : Finite (S r) := hli.finite
  let : Fintype (S r) := Fintype.ofFinite _
  have hcard : Fintype.card (S r) = d := by
    calc
      _ = Module.finrank ℂ (EuclideanVector d) := (Module.finrank_eq_card_basis B0).symm
      _ = d := finrank_euclideanSpace_fin
  let e : S r ≃ Fin d := Fintype.equivFinOfCardEq hcard
  let B : Module.Basis (Fin d) ℂ (EuclideanVector d) := B0.reindex e
  have hrange : Set.range B = S r := by
    rw [Module.Basis.range_reindex]
    simp only [B0, Module.Basis.coe_mk, Subtype.range_coe]
  refine ⟨B, fun i => le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    exact hj
  · have hsi : Submodule.span ℂ (S i.val) = F i := by rw [(hS i.val).2, hindexi i]
    rw [← hsi]
    apply Submodule.span_mono
    intro x hx
    have hxr : x ∈ S r := hSmono (Nat.le_of_lt_succ i.isLt) hx
    obtain ⟨j, hj⟩ := hrange.symm ▸ hxr
    refine ⟨j, ?_, hj⟩
    change B j ∈ Submodule.span ℂ (S i.val)
    rw [hj]
    exact Submodule.subset_span hx

#print axioms exists_basis_spanning_chain
#assert_trust kernel exists_basis_spanning_chain

end NLA.MF06

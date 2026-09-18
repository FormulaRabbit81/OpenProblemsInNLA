/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md. Mathlib supplies
monicity, exact degrees, roots of multiset products and complete complex splitting.

The scalar is complex and nonzero. Positivity requires the later sum-of-squares
argument and is not assumed here; the constant polynomial -1 remains admissible.
-/
import NLA.IE02.ReciprocalRoots

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open Polynomial

private theorem root_partition_factor (P : Poly) (s : Multiset ℂ) (hP : P ≠ 0)
    (hpartition : P.roots = s + s.map reciprocalConj) (hs : ∀ z ∈ s, z ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ P = C κ *
      (rootProduct s * conjReflect s.card (rootProduct s)) := by
  classical
  let d : ℂ := (s.map (fun z => -star z)).prod
  have hd : d ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hmem
    obtain ⟨z, hz, heq⟩ := Multiset.mem_map.mp hmem
    exact (neg_ne_zero.mpr (star_ne_zero.mpr (hs z hz))) heq
  have hfactor : P = C P.leadingCoeff *
      (rootProduct s * rootProduct (s.map reciprocalConj)) := by
    calc
      P = C P.leadingCoeff * rootProduct P.roots := by
        simpa only [rootProduct] using (IsAlgClosed.splits P).eq_prod_roots
      _ = C P.leadingCoeff * rootProduct (s + s.map reciprocalConj) := by
        rw [hpartition]
      _ = _ := by simp only [rootProduct, Multiset.map_add, Multiset.prod_add]
  have hreflection : conjReflect s.card (rootProduct s) =
      C d * rootProduct (s.map reciprocalConj) := rootProduct_reflection s hs
  let κ : ℂ := P.leadingCoeff * d⁻¹
  have hκ : κ ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hP) (inv_ne_zero hd)
  have hscale : κ * d = P.leadingCoeff := by
    dsimp only [κ]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  refine ⟨κ, hκ, ?_⟩
  -- The root partition already factors P. Cancel only the nonzero scalar
  -- introduced by reflection, avoiding a second roots/factorization proof.
  rw [hreflection]
  calc
    P = C P.leadingCoeff * (rootProduct s * rootProduct (s.map reciprocalConj)) := hfactor
    _ = (C κ * C d) * (rootProduct s * rootProduct (s.map reciprocalConj)) := by
      rw [← C_mul, hscale]
    _ = C κ * (rootProduct s * (C d * rootProduct (s.map reciprocalConj))) := by ring

theorem reciprocal_inside_factor (ell : ℕ) (P : Poly)
    (hdeg : P.degree = (2 * ell : WithBot ℕ)) (hzero : P.coeff 0 ≠ 0)
    (href : conjReflect (2 * ell) P = P)
    (hcircle : ∀ z : ℂ, ‖z‖ = 1 → P.eval z ≠ 0) :
    (rootProduct (insideRoots P)).degree = (ell : WithBot ℕ) ∧
    (rootProduct (insideRoots P)).eval 0 ≠ 0 ∧
    (∀ z : ℂ, ‖z‖ = 1 → (rootProduct (insideRoots P)).eval z ≠ 0) ∧
    ∃ κ : ℂ, κ ≠ 0 ∧ P = C κ *
      (rootProduct (insideRoots P) * conjReflect ell (rootProduct (insideRoots P))) := by
  classical
  obtain ⟨_hpair, hpartition, hcard, hnonzero⟩ :=
    reciprocal_root_pairing ell P hdeg hzero href hcircle
  have hP : P ≠ 0 := by
    intro h
    apply hzero
    simp [h]
  have hs : ∀ z ∈ insideRoots P, z ≠ 0 := by
    intro z hz
    exact hnonzero z (Multiset.mem_filter.mp hz).1
  -- These are direct library facts about the exact frozen mapped product.
  -- Monicity also proves it is nonzero in the empty-product case ell = 0.
  have hmonic : (rootProduct (insideRoots P)).Monic :=
    monic_multisetProd_X_sub_C (insideRoots P)
  have hproduct : rootProduct (insideRoots P) ≠ 0 := hmonic.ne_zero
  have hnat : (rootProduct (insideRoots P)).natDegree = (insideRoots P).card :=
    natDegree_multiset_prod_X_sub_C_eq_card (insideRoots P)
  have hdegree : (rootProduct (insideRoots P)).degree = (ell : WithBot ℕ) := by
    rw [degree_eq_natDegree hproduct, hnat, hcard]
  have hroots : (rootProduct (insideRoots P)).roots = insideRoots P :=
    roots_multiset_prod_X_sub_C (insideRoots P)
  have hatzero : (rootProduct (insideRoots P)).eval 0 ≠ 0 := by
    intro heval
    have hmem := (mem_roots hproduct).mpr heval
    rw [hroots] at hmem
    exact hs 0 hmem rfl
  have hatcircle : ∀ z : ℂ, ‖z‖ = 1 → (rootProduct (insideRoots P)).eval z ≠ 0 := by
    intro z hnorm heval
    have hmem := (mem_roots hproduct).mpr heval
    rw [hroots] at hmem
    exact (ne_of_lt (Multiset.mem_filter.mp hmem).2) hnorm
  obtain ⟨κ, hκ, hfactor⟩ := root_partition_factor P (insideRoots P) hP hpartition hs
  rw [hcard] at hfactor
  exact ⟨hdegree, hatzero, hatcircle, κ, hκ, hfactor⟩

#print axioms reciprocal_inside_factor
#assert_trust kernel reciprocal_inside_factor

end
end NLA.IE02

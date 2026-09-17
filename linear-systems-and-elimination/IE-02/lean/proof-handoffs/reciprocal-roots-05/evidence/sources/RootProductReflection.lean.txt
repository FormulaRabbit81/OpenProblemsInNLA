/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md. Fixed-bound reflection
uses Mathlib's Polynomial.Reverse development and the existing reflection_product.

The full multiset, including repeated factors and the empty product, is retained.
Every root is nonzero before the reciprocal linear-factor identity is used.
-/
import NLA.IE02.Reflection
import Mathlib.Algebra.BigOperators.Ring.Multiset

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open Polynomial

theorem rootProduct_reflection (s : Multiset ℂ) (hs : ∀ z ∈ s, z ≠ 0) :
    conjReflect s.card (rootProduct s) =
      C ((s.map (fun z => -star z)).prod) * rootProduct (s.map reciprocalConj) := by
  classical
  -- Carry the nonzero-factor premise through the induction so it applies to
  -- each remaining multiset, without selecting or discarding multiplicities.
  revert hs
  refine Multiset.induction_on s ?_ ?_
  · intro _hs
    simp [rootProduct, conjReflect]
  · intro z t ih hs
    have hz : z ≠ 0 := hs z (by simp)
    have ht : ∀ a ∈ t, a ≠ 0 := fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    have hdegree : DegreeLE (rootProduct t) t.card := by
      unfold DegreeLE rootProduct
      exact degree_le_of_natDegree_le (natDegree_multiset_prod_X_sub_C_eq_card t).le
    -- Reflection of one actual degree-one factor uses named map/reflect APIs.
    -- Only its scalar normalization needs the explicitly nonzero conjugate.
    have hlinear : conjReflect 1 (X - C z) =
        C (-star z) * (X - C (reciprocalConj z)) := by
      have hcancel : C (star z) * C ((star z)⁻¹) = (1 : Poly) := by
        rw [← C_mul, mul_inv_cancel₀ (star_ne_zero.mpr hz), C_1]
      calc
        conjReflect 1 (X - C z) = 1 - C (star z) * X := by
          simp only [conjReflect, Polynomial.map_sub, Polynomial.map_X,
            Polynomial.map_C, starRingEnd_apply, reflect_sub, reflect_one_X,
            reflect_C, pow_one]
        _ = C (-star z) * (X - C (reciprocalConj z)) := by
          simp only [reciprocalConj, C_neg, mul_sub, neg_mul]
          rw [hcancel]
          ring
    calc
      conjReflect (z ::ₘ t).card (rootProduct (z ::ₘ t)) =
          conjReflect (1 + t.card) ((X - C z) * rootProduct t) := by
        simp only [Multiset.card_cons, rootProduct, Multiset.map_cons,
          Multiset.prod_cons, Nat.add_comm]
      _ = conjReflect 1 (X - C z) * conjReflect t.card (rootProduct t) :=
        reflection_product 1 t.card (X - C z) (rootProduct t)
          (degree_X_sub_C_le z) hdegree
      _ = (C (-star z) * (X - C (reciprocalConj z))) *
          (C ((t.map (fun a => -star a)).prod) * rootProduct (t.map reciprocalConj)) := by
        rw [hlinear, ih ht]
      _ = C (((z ::ₘ t).map (fun a => -star a)).prod) *
          rootProduct ((z ::ₘ t).map reciprocalConj) := by
        simp only [rootProduct, Multiset.map_cons, Multiset.prod_cons, C_mul]
        ring

#print axioms rootProduct_reflection
#assert_trust kernel rootProduct_reflection

end
end NLA.IE02

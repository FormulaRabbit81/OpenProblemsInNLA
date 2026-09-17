/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu posed the coefficient
question; Matthew J. Colbrook proved the full identity. This final assembly
uses the proved universal minor relation and actual positive Sinkhorn scaling.
-/
import NLA.NM04.BalancedMinor
import NLA.NM04.PencilConsequences
import NLA.NM04.SinkhornSemantics
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix

theorem balanced_null_vector {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (hS : Positive S) (hB : Balanced S) :
    (pencil S hm hn (S (firstIndex hm) (firstIndex hn))).mulVec (weight m n) = 0 ∧
    weight m n (emptyIndex (Tail m) (Tail n)) = 1 ∧ weight m n ≠ 0 := by
  exact ⟨pencil_kernel_of_minor_relation hm hn S
    (balanced_minor_relation hm hn S hS hB), weight_empty m n, weight_nonzero m n⟩

#print axioms balanced_null_vector
#assert_trust kernel balanced_null_vector

theorem sinkhorn_pencil_singular {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) :
    ∃ v : Index m n → ℝ, 0 < v (emptyIndex (Tail m) (Tail n)) ∧
      (pencil A hm hn ((sinkhorn A) (firstIndex hm) (firstIndex hn))).mulVec v = 0 := by
  obtain ⟨hscaled, hpos, _⟩ := sinkhorn_semantics hm hn A hA
  obtain ⟨a, b, ha, hb, heq, hbalanced⟩ := hscaled
  apply transport_scaled_pencil_kernel hm hn A a b ha hb
  rw [← heq]
  exact (balanced_null_vector hm hn (sinkhorn A) hpos hbalanced).1

#print axioms sinkhorn_pencil_singular
#assert_trust kernel sinkhorn_pencil_singular

theorem rowland_wu_identity {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) :
    (∑ E : Finset (Index m n),
      ((m : ℝ)⁻¹ • (HReal m n).submatrix
        (Subtype.val : E → Index m n) (Subtype.val : E → Index m n)).det *
      (∏ I ∈ E, delta A hm hn I) * (∏ I ∈ (Finset.univ \ E), gamma A hm hn I) *
      ((sinkhorn A) (firstIndex hm) (firstIndex hn)) ^ E.card) = 0 := by
  obtain ⟨v, hv, hnull⟩ := sinkhorn_pencil_singular hm hn A hA
  exact coefficient_sum_of_pencil_kernel hm hn A
    ((sinkhorn A) (firstIndex hm) (firstIndex hn)) v hv hnull

#print axioms rowland_wu_identity
#assert_trust kernel rowland_wu_identity

end
end NLA.NM04

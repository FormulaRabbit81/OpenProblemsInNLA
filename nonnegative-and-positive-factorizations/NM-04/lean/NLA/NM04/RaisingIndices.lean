/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

Actual enlarged minor indices and the full literal raising operator.
-/
import NLA.NM04.TransitionSupport
import Mathlib.Data.Fintype.BigOperators
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v w

/-- Adjoin an actually unselected row and column. -/
def raisingIndex {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (I : MinorIndex α β) (s : {s : α // s ∉ I.1.1}) (t : {t : β // t ∉ I.1.2}) :
    MinorIndex α β :=
  ⟨(insert s.val I.1.1, insert t.val I.1.2), by
    rw [Finset.card_insert_of_notMem s.property, Finset.card_insert_of_notMem t.property]
    exact congrArg (fun n : ℕ => n + 1) I.property⟩

theorem raisingIndex_support {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β)
    (s : {s : α // s ∉ I.1.1}) (t : {t : β // t ∉ I.1.2}) :
    RaisingSupport I (raisingIndex I s t) s t := by
  change I.1.1 \ insert s.val I.1.1 = ∅ ∧ insert s.val I.1.1 \ I.1.1 = {s.val} ∧
    I.1.2 \ insert t.val I.1.2 = ∅ ∧ insert t.val I.1.2 \ I.1.2 = {t.val}
  exact ⟨Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert _ _),
    Finset.insert_sdiff_cancel s.property,
    Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert _ _),
    Finset.insert_sdiff_cancel t.property⟩

theorem raisingSupport_index {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] {I J : MinorIndex α β} {s : α} {t : β}
    (h : RaisingSupport I J s t) :
    ∃ s' : {s : α // s ∉ I.1.1}, ∃ t' : {t : β // t ∉ I.1.2},
      raisingIndex I s' t' = J := by
  have hs : s ∉ I.1.1 :=
    (Finset.mem_sdiff.mp (h.2.1.symm ▸ Finset.mem_singleton_self s)).2
  have ht : t ∉ I.1.2 :=
    (Finset.mem_sdiff.mp (h.2.2.2.symm ▸ Finset.mem_singleton_self t)).2
  refine ⟨⟨s, hs⟩, ⟨t, ht⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change insert s I.1.1 = J.1.1
    calc
      _ = {s} ∪ I.1.1 := (Finset.singleton_union _ _).symm
      _ = (J.1.1 \ I.1.1) ∪ I.1.1 := congrArg (fun U => U ∪ I.1.1) h.2.1.symm
      _ = J.1.1 := Finset.sdiff_union_of_subset (Finset.sdiff_eq_empty_iff_subset.mp h.1)
  · change insert t I.1.2 = J.1.2
    calc
      _ = {t} ∪ I.1.2 := (Finset.singleton_union _ _).symm
      _ = (J.1.2 \ I.1.2) ∪ I.1.2 := congrArg (fun U => U ∪ I.1.2) h.2.2.2.symm
      _ = J.1.2 := Finset.sdiff_union_of_subset (Finset.sdiff_eq_empty_iff_subset.mp h.2.2.1)

theorem raisingIndex_injective {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β) :
    Function.Injective (fun p : {s : α // s ∉ I.1.1} × {t : β // t ∉ I.1.2} =>
      raisingIndex I p.1 p.2) := by
  intro p q hpq
  change raisingIndex I p.1 p.2 = raisingIndex I q.1 q.2 at hpq
  have hp := raisingIndex_support I p.1 p.2
  have hq : RaisingSupport I (raisingIndex I p.1 p.2) q.1 q.2 := by
    rw [hpq]
    exact raisingIndex_support I q.1 q.2
  have h := (hp.iff_eq q.1 q.2).mp hq
  exact Prod.ext (Subtype.ext h.1.symm) (Subtype.ext h.2.symm)

/-- Every supported term is present once, and every term outside this image is zero. -/
theorem raising_eq_index_sum {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (f : MinorIndex α β → 𝕜) (I : MinorIndex α β) :
    raising f I = ∑ s : {s : α // s ∉ I.1.1}, ∑ t : {t : β // t ∉ I.1.2},
      (-1 : 𝕜) ^ (position (s : α) (raisingIndex I s t).1.1 +
        position (t : β) (raisingIndex I s t).1.2) * f (raisingIndex I s t) := by
  symm
  calc
    _ = ∑ p : {s : α // s ∉ I.1.1} × {t : β // t ∉ I.1.2},
        (-1 : 𝕜) ^ (position (p.1 : α) (raisingIndex I p.1 p.2).1.1 +
          position (p.2 : β) (raisingIndex I p.1 p.2).1.2) *
            f (raisingIndex I p.1 p.2) := (Fintype.sum_prod_type _).symm
    _ = raising f I := by
      unfold raising
      apply Fintype.sum_of_injective
        (fun p : {s : α // s ∉ I.1.1} × {t : β // t ∉ I.1.2} => raisingIndex I p.1 p.2)
        (raisingIndex_injective I)
      · intro J hJ
        have hzero : raisingCoefficient I J = 0 := raisingCoefficient_zero (by
          intro s t hst
          obtain ⟨s', t', he⟩ := raisingSupport_index hst
          exact hJ ⟨(s', t'), he⟩)
        simp only [hzero, Int.cast_zero, zero_mul]
      · intro p
        rw [raisingCoefficient_of_support (raisingIndex_support I p.1 p.2)]
        simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

#print axioms raisingIndex_support
#assert_trust kernel raisingIndex_support
#print axioms raisingSupport_index
#assert_trust kernel raisingSupport_index
#print axioms raisingIndex_injective
#assert_trust kernel raisingIndex_injective
#print axioms raising_eq_index_sum
#assert_trust kernel raising_eq_index_sum

end
end NLA.NM04

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The actual index obtained by exchanging a selected column for an unselected one.
-/
import NLA.NM04.DecisionTransport
import Mathlib.Data.Fintype.BigOperators
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v w

/-- This index keeps the rows, removes the selected column, and inserts an
actually unselected column. Its cardinality proof uses those membership facts. -/
def columnExchangeIndex {α : Type u} {β : Type v} [DecidableEq β]
    (I : MinorIndex α β) (s : I.1.2) (t : {t : β // t ∉ I.1.2}) : MinorIndex α β :=
  ⟨(I.1.1, insert t.val (I.1.2.erase s.val)), by
    have ht : t.val ∉ I.1.2.erase s.val := fun h => t.property (Finset.mem_of_mem_erase h)
    have hc : 1 ≤ I.1.2.card := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨s.val, s.property⟩)
    rw [Finset.card_insert_of_notMem ht, Finset.card_erase_of_mem s.property,
      Nat.sub_add_cancel hc]
    exact I.property⟩

theorem columnExchangeIndex_support {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β)
    (s : I.1.2) (t : {t : β // t ∉ I.1.2}) :
    ColumnExchangeSupport I (columnExchangeIndex I s t) s t := by
  change I.1.1 \ I.1.1 = ∅ ∧ I.1.1 \ I.1.1 = ∅ ∧
    I.1.2 \ insert t.val (I.1.2.erase s.val) = {s.val} ∧
    insert t.val (I.1.2.erase s.val) \ I.1.2 = {t.val}
  refine ⟨Finset.sdiff_self _, Finset.sdiff_self _, ?_, ?_⟩
  · exact (Finset.sdiff_insert_of_notMem t.property _).trans
      (Finset.sdiff_erase_self s.property)
  · rw [Finset.insert_sdiff_of_notMem _ t.property,
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _)]
    rfl

/-- Every literal exchange support is attained by exactly the specified index. -/
theorem columnExchangeSupport_index {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] {I J : MinorIndex α β} {s t : β}
    (h : ColumnExchangeSupport I J s t) :
    ∃ s' : I.1.2, ∃ t' : {t : β // t ∉ I.1.2}, columnExchangeIndex I s' t' = J := by
  have hs : s ∈ I.1.2 :=
    (Finset.mem_sdiff.mp (h.2.2.1.symm ▸ Finset.mem_singleton_self s)).1
  have ht : t ∉ I.1.2 :=
    (Finset.mem_sdiff.mp (h.2.2.2.symm ▸ Finset.mem_singleton_self t)).2
  have hrows : I.1.1 = J.1.1 := Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp h.1)
    (Finset.sdiff_eq_empty_iff_subset.mp h.2.1)
  have hcommon : I.1.2.erase s = I.1.2 ∩ J.1.2 := by
    calc
      _ = I.1.2 \ {s} := Finset.erase_eq _ _
      _ = I.1.2 \ (I.1.2 \ J.1.2) := congrArg (fun U => I.1.2 \ U) h.2.2.1.symm
      _ = _ := Finset.sdiff_sdiff_self_left _ _
  refine ⟨⟨s, hs⟩, ⟨t, ht⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hrows
  · change insert t (I.1.2.erase s) = J.1.2
    calc
      _ = {t} ∪ (I.1.2 ∩ J.1.2) := by rw [hcommon, Finset.singleton_union]
      _ = (J.1.2 \ I.1.2) ∪ (J.1.2 ∩ I.1.2) := by rw [h.2.2.2, Finset.inter_comm]
      _ = J.1.2 := Finset.sdiff_union_inter _ _

theorem columnExchangeIndex_injective {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β) :
    Function.Injective (fun p : I.1.2 × {t : β // t ∉ I.1.2} =>
      columnExchangeIndex I p.1 p.2) := by
  intro p q hpq
  change columnExchangeIndex I p.1 p.2 = columnExchangeIndex I q.1 q.2 at hpq
  have hp := columnExchangeIndex_support I p.1 p.2
  have hq : ColumnExchangeSupport I (columnExchangeIndex I p.1 p.2) q.1 q.2 := by
    rw [hpq]
    exact columnExchangeIndex_support I q.1 q.2
  have h := (hp.iff_eq q.1 q.2).mp hq
  exact Prod.ext (Subtype.ext h.1.symm) (Subtype.ext h.2.symm)

/-- Reindex the complete exchange operator, with zero contribution off the
image, and preserve its integer sign when casting into any commutative ring. -/
theorem columnExchange_eq_index_sum {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [DecidableEq α] [LinearOrder β] [CommRing 𝕜]
    (f : MinorIndex α β → 𝕜) (I : MinorIndex α β) :
    columnExchange f I = ∑ s : I.1.2, ∑ t : {t : β // t ∉ I.1.2},
      (-1 : 𝕜) ^ (position (s : β) I.1.2 +
        position (t : β) (columnExchangeIndex I s t).1.2) * f (columnExchangeIndex I s t) := by
  symm
  calc
    _ = ∑ p : I.1.2 × {t : β // t ∉ I.1.2},
        (-1 : 𝕜) ^ (position (p.1 : β) I.1.2 +
          position (p.2 : β) (columnExchangeIndex I p.1 p.2).1.2) *
            f (columnExchangeIndex I p.1 p.2) := (Fintype.sum_prod_type _).symm
    _ = columnExchange f I := by
      unfold columnExchange
      apply Fintype.sum_of_injective
        (fun p : I.1.2 × {t : β // t ∉ I.1.2} => columnExchangeIndex I p.1 p.2)
        (columnExchangeIndex_injective I)
      · intro J hJ
        have hzero : columnExchangeCoefficient I J = 0 := by
          apply column_coefficient_all_decisions I J 0
          apply columnExchangeCoefficient_zero
          intro s t hst
          have hst' : ColumnExchangeSupport I J s t := support_decision_transport
            (fun da db => @ColumnExchangeSupport α β da db I J s t) hst
          obtain ⟨s', t', he⟩ := columnExchangeSupport_index hst'
          exact hJ ⟨(s', t'), he⟩
        simp only [hzero, Int.cast_zero, zero_mul]
      · intro p
        have hcoefficient : columnExchangeCoefficient I (columnExchangeIndex I p.1 p.2) =
            (-1 : ℤ) ^ (position (p.1 : β) I.1.2 +
              position (p.2 : β) (columnExchangeIndex I p.1 p.2).1.2) := by
          apply column_coefficient_all_decisions I (columnExchangeIndex I p.1 p.2)
          apply columnExchangeCoefficient_of_support
          exact support_decision_transport
            (fun da db => @ColumnExchangeSupport α β da db I
              (columnExchangeIndex I p.1 p.2) p.1 p.2)
            (columnExchangeIndex_support I p.1 p.2)
        rw [hcoefficient]
        simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

#print axioms columnExchangeIndex_support
#assert_trust kernel columnExchangeIndex_support
#print axioms columnExchangeSupport_index
#assert_trust kernel columnExchangeSupport_index
#print axioms columnExchangeIndex_injective
#assert_trust kernel columnExchangeIndex_injective
#print axioms columnExchange_eq_index_sum
#assert_trust kernel columnExchange_eq_index_sum

end
end NLA.NM04

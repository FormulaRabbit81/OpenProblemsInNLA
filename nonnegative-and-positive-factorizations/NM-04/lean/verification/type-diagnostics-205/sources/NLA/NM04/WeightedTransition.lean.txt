/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Mathematical source: Matthew J. Colbrook.
The literal finite transition matrix acts on the cardinality weights. All
dimensions remain symbolic and every unsupported coefficient is proved zero.
-/
import NLA.NM04.DecisionTransport
import NLA.NM04.TransitionCardinality
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

private theorem column_support_not_self {α β : Type*}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β) (s t : β) :
    ¬ ColumnExchangeSupport I I s t := by
  intro h
  exact Finset.empty_ne_singleton s ((Finset.sdiff_self I.1.2).symm.trans h.2.2.1)

private theorem row_support_not_self {α β : Type*}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β) (s t : α) :
    ¬ RowExchangeSupport I I s t := by
  intro h
  exact Finset.empty_ne_singleton s ((Finset.sdiff_self I.1.1).symm.trans h.1)

private theorem raising_self_zero {α β : Type*} [Fintype α] [Fintype β]
    [LinearOrder α] [LinearOrder β] (I : MinorIndex α β) :
    raisingCoefficient I I = 0 := by
  apply raisingCoefficient_zero
  intro s t h
  exact Finset.empty_ne_singleton s ((Finset.sdiff_self I.1.1).symm.trans h.2.1)

private theorem lowering_self_zero {α β : Type*} [Fintype α] [Fintype β]
    [LinearOrder α] [LinearOrder β] (I : MinorIndex α β) :
    loweringCoefficient I I = 0 := by
  apply loweringCoefficient_zero
  intro s t h
  exact Finset.empty_ne_singleton s ((Finset.sdiff_self I.1.1).symm.trans h.1)

private theorem column_self_zero {α β : Type*} [Fintype β] [LinearOrder β]
    (I : MinorIndex α β) : columnExchangeCoefficient I I = 0 :=
  columnExchangeCoefficient_zero (column_support_not_self I)

private theorem row_self_zero {α β : Type*} [Fintype α] [LinearOrder α]
    (I : MinorIndex α β) : rowExchangeCoefficient I I = 0 :=
  rowExchangeCoefficient_zero (row_support_not_self I)

private theorem raising_weight {m n : ℕ} (hm : 1 ≤ m) (I J : Index m n) :
    (m : ℝ) * (raisingCoefficient I J : ℝ) * weight m n J =
      weight m n I * (n : ℝ) * (raisingCoefficient I J : ℝ) := by
  by_cases h : ∃ s t, RaisingSupport I J s t
  · obtain ⟨s, t, h⟩ := h
    have hw := weight_raising_card hm I J h.card
    calc
      _ = (raisingCoefficient I J : ℝ) * ((m : ℝ) * weight m n J) := by ring
      _ = (raisingCoefficient I J : ℝ) * ((n : ℝ) * weight m n I) :=
        congrArg (fun x : ℝ => (raisingCoefficient I J : ℝ) * x) hw
      _ = _ := by ring
  · have hz : raisingCoefficient I J = 0 := by
      apply raisingCoefficient_zero
      intro s t hs
      exact h ⟨s, t, support_decision_transport
        (fun da db => @RaisingSupport (Tail m) (Tail n) da db I J s t) hs⟩
    rw [hz]
    simp

private theorem lowering_weight {m n : ℕ} (hm : 1 ≤ m) (I J : Index m n) :
    (n : ℝ) * (loweringCoefficient I J : ℝ) * weight m n J =
      weight m n I * (m : ℝ) * (loweringCoefficient I J : ℝ) := by
  by_cases h : ∃ s t, LoweringSupport I J s t
  · obtain ⟨s, t, h⟩ := h
    have hw := weight_lowering_card hm I J h.card
    calc
      _ = (loweringCoefficient I J : ℝ) * ((n : ℝ) * weight m n J) := by ring
      _ = (loweringCoefficient I J : ℝ) * ((m : ℝ) * weight m n I) :=
        congrArg (fun x : ℝ => (loweringCoefficient I J : ℝ) * x) hw
      _ = _ := by ring
  · have hz : loweringCoefficient I J = 0 := by
      apply loweringCoefficient_zero
      intro s t hs
      exact h ⟨s, t, support_decision_transport
        (fun da db => @LoweringSupport (Tail m) (Tail n) da db I J s t) hs⟩
    rw [hz]
    simp

private theorem column_weight {m n : ℕ} (I J : Index m n) :
    (columnExchangeCoefficient I J : ℝ) * weight m n J =
      weight m n I * (columnExchangeCoefficient I J : ℝ) := by
  by_cases h : ∃ s t, ColumnExchangeSupport I J s t
  · obtain ⟨s, t, h⟩ := h
    rw [weight_exchange_card I J h.card]
    ring
  · have hz : columnExchangeCoefficient I J = 0 := by
      apply column_coefficient_all_decisions I J 0
      apply columnExchangeCoefficient_zero
      intro s t hs
      exact h ⟨s, t, support_decision_transport
        (fun da db => @ColumnExchangeSupport (Tail m) (Tail n) da db I J s t) hs⟩
    rw [hz]
    simp

private theorem row_weight {m n : ℕ} (I J : Index m n) :
    (rowExchangeCoefficient I J : ℝ) * weight m n J =
      weight m n I * (rowExchangeCoefficient I J : ℝ) := by
  by_cases h : ∃ s t, RowExchangeSupport I J s t
  · obtain ⟨s, t, h⟩ := h
    rw [weight_exchange_card I J h.card]
    ring
  · have hz : rowExchangeCoefficient I J = 0 := by
      apply row_coefficient_all_decisions I J 0
      apply rowExchangeCoefficient_zero
      intro s t hs
      exact h ⟨s, t, support_decision_transport
        (fun da db => @RowExchangeSupport (Tail m) (Tail n) da db I J s t) hs⟩
    rw [hz]
    simp

private theorem HReal_decomposition (m n : ℕ) (I J : Index m n) :
    HReal m n I J =
      (if I = J then (I.1.1.card : ℝ) * ((m : ℝ) + (n : ℝ)) -
        (m : ℝ) * (n : ℝ) else 0) +
      (m : ℝ) * (raisingCoefficient I J : ℝ) -
      (n : ℝ) * (loweringCoefficient I J : ℝ) +
      (m : ℝ) * (columnExchangeCoefficient I J : ℝ) +
      (n : ℝ) * (rowExchangeCoefficient I J : ℝ) := by
  by_cases h : I = J
  · subst J
    have hU : raisingCoefficient I I = 0 := raising_self_zero I
    have hL : loweringCoefficient I I = 0 := lowering_self_zero I
    have hC : columnExchangeCoefficient I I = 0 :=
      column_coefficient_all_decisions I I 0 (column_self_zero I) _
    have hR : rowExchangeCoefficient I I = 0 :=
      row_coefficient_all_decisions I I 0 (row_self_zero I) _
    simp [HReal, H, hU, hL, hC, hR]
  · simp only [HReal, H, if_neg h, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, zero_add]

theorem weighted_transition_action {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (f : Index m n → ℝ) (I : Index m n) :
    (HReal m n * Matrix.diagonal f).mulVec (weight m n) I =
      weight m n I *
        (((I.1.1.card : ℝ) * ((m : ℝ) + (n : ℝ)) - (m : ℝ) * (n : ℝ)) * f I +
          (n : ℝ) * raising f I - (m : ℝ) * lowering f I +
          (m : ℝ) * columnExchange f I + (n : ℝ) * rowExchange f I) := by
  -- The frozen canonical contract retains hn; this weight identity only needs hm.
  change (∑ J, (HReal m n * Matrix.diagonal f) I J * weight m n J) = _
  simp only [Matrix.mul_diagonal]
  let D : ℝ := (I.1.1.card : ℝ) * ((m : ℝ) + (n : ℝ)) - (m : ℝ) * (n : ℝ)
  have hterm (J : Index m n) :
      (HReal m n I J * f J) * weight m n J =
        (if I = J then weight m n I * D * f I else 0) +
        (weight m n I * (n : ℝ)) * ((raisingCoefficient I J : ℝ) * f J) -
        (weight m n I * (m : ℝ)) * ((loweringCoefficient I J : ℝ) * f J) +
        (weight m n I * (m : ℝ)) * ((columnExchangeCoefficient I J : ℝ) * f J) +
        (weight m n I * (n : ℝ)) * ((rowExchangeCoefficient I J : ℝ) * f J) := by
    have hd : (if I = J then D else 0) * f J * weight m n J =
        (if I = J then weight m n I * D * f I else 0) := by
      by_cases h : I = J
      · subst J
        simp only [ite_true]
        ring
      · simp only [if_neg h, zero_mul]
    rw [HReal_decomposition]
    change (((if I = J then D else 0) +
      (m : ℝ) * (raisingCoefficient I J : ℝ) -
      (n : ℝ) * (loweringCoefficient I J : ℝ) +
      (m : ℝ) * (columnExchangeCoefficient I J : ℝ) +
      (n : ℝ) * (rowExchangeCoefficient I J : ℝ)) * f J) * weight m n J = _
    calc
      _ = (if I = J then D else 0) * f J * weight m n J +
          ((m : ℝ) * (raisingCoefficient I J : ℝ) * weight m n J) * f J -
          ((n : ℝ) * (loweringCoefficient I J : ℝ) * weight m n J) * f J +
          (m : ℝ) * ((columnExchangeCoefficient I J : ℝ) * weight m n J) * f J +
          (n : ℝ) * ((rowExchangeCoefficient I J : ℝ) * weight m n J) * f J := by ring
      _ = _ := by
        rw [hd, raising_weight hm I J, lowering_weight hm I J,
          column_weight I J, row_weight I J]
        ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold raising lowering columnExchange rowExchange
  dsimp only [D]
  ring

#print axioms weighted_transition_action
#assert_trust kernel weighted_transition_action

end
end NLA.NM04

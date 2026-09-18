/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Supporting subset cardinalities for the
unchanged NM-04 weighted-transition contract; mathematical source: Colbrook.
-/
import NLA.NM04.Definitions
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
universe u v

section
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
variable {I J : MinorIndex α β}

theorem RaisingSupport.card {s : α} {t : β} (h : RaisingSupport I J s t) :
    J.1.1.card = I.1.1.card + 1 := by
  have hsub : I.1.1 ⊆ J.1.1 := Finset.sdiff_eq_empty_iff_subset.mp h.1
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [h.2.1, Finset.card_singleton] at hc
  omega

theorem LoweringSupport.card {s : α} {t : β} (h : LoweringSupport I J s t) :
    I.1.1.card = J.1.1.card + 1 := by
  have hu : RaisingSupport J I s t := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩
  exact hu.card

theorem ColumnExchangeSupport.card {s t : β} (h : ColumnExchangeSupport I J s t) :
    I.1.1.card = J.1.1.card := by
  have he : I.1.1 = J.1.1 := Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp h.1)
    (Finset.sdiff_eq_empty_iff_subset.mp h.2.1)
  exact congrArg Finset.card he

theorem RowExchangeSupport.card {s t : α} (h : RowExchangeSupport I J s t) :
    I.1.1.card = J.1.1.card := by
  have hi := Finset.card_sdiff_add_card_inter I.1.1 J.1.1
  have hj := Finset.card_sdiff_add_card_inter J.1.1 I.1.1
  rw [h.1, Finset.card_singleton] at hi
  rw [h.2.1, Finset.card_singleton, Finset.inter_comm J.1.1 I.1.1] at hj
  omega

end

theorem weight_raising_card {m n : ℕ} (hm : 1 ≤ m) (I J : Index m n)
    (h : J.1.1.card = I.1.1.card + 1) :
    (m : ℝ) * weight m n J = (n : ℝ) * weight m n I := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold weight
  rw [h, pow_succ]
  field_simp

theorem weight_lowering_card {m n : ℕ} (hm : 1 ≤ m) (I J : Index m n)
    (h : I.1.1.card = J.1.1.card + 1) :
    (n : ℝ) * weight m n J = (m : ℝ) * weight m n I :=
  (weight_raising_card hm J I h).symm

theorem weight_exchange_card {m n : ℕ} (I J : Index m n)
    (h : I.1.1.card = J.1.1.card) : weight m n I = weight m n J := by
  unfold weight
  rw [h]

#print axioms RaisingSupport.card
#print axioms LoweringSupport.card
#print axioms ColumnExchangeSupport.card
#print axioms RowExchangeSupport.card
#print axioms weight_raising_card
#print axioms weight_lowering_card
#print axioms weight_exchange_card
#assert_trust kernel RaisingSupport.card
#assert_trust kernel LoweringSupport.card
#assert_trust kernel ColumnExchangeSupport.card
#assert_trust kernel RowExchangeSupport.card
#assert_trust kernel weight_raising_card
#assert_trust kernel weight_lowering_card
#assert_trust kernel weight_exchange_card

end NLA.NM04

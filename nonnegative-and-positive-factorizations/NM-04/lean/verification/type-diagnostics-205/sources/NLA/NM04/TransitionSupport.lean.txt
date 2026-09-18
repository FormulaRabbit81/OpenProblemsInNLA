/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

Singleton support witnesses are unique, and the four transition types are disjoint.
All types and selected subset cardinalities remain arbitrary.
-/
import NLA.NM04.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

namespace NLA.NM04

-- Match the frozen definitions and Challenge decision instances.
attribute [local instance] Classical.propDecidable

open scoped BigOperators
universe u v
variable {α : Type u} {β : Type v}

section Support
variable [DecidableEq α] [DecidableEq β] {I J : MinorIndex α β}

theorem RaisingSupport.iff_eq {s : α} {t : β} (h : RaisingSupport I J s t)
    (a : α) (b : β) : RaisingSupport I J a b ↔ a = s ∧ b = t := by
  constructor
  · intro hab
    exact ⟨Finset.singleton_inj.mp (hab.2.1.symm.trans h.2.1),
      Finset.singleton_inj.mp (hab.2.2.2.symm.trans h.2.2.2)⟩
  · rintro ⟨rfl, rfl⟩
    exact h

theorem LoweringSupport.iff_eq {s : α} {t : β} (h : LoweringSupport I J s t)
    (a : α) (b : β) : LoweringSupport I J a b ↔ a = s ∧ b = t := by
  constructor
  · intro hab
    exact ⟨Finset.singleton_inj.mp (hab.1.symm.trans h.1),
      Finset.singleton_inj.mp (hab.2.2.1.symm.trans h.2.2.1)⟩
  · rintro ⟨rfl, rfl⟩
    exact h

theorem ColumnExchangeSupport.iff_eq {s t : β} (h : ColumnExchangeSupport I J s t)
    (a b : β) : ColumnExchangeSupport I J a b ↔ a = s ∧ b = t := by
  constructor
  · intro hab
    exact ⟨Finset.singleton_inj.mp (hab.2.2.1.symm.trans h.2.2.1),
      Finset.singleton_inj.mp (hab.2.2.2.symm.trans h.2.2.2)⟩
  · rintro ⟨rfl, rfl⟩
    exact h

theorem RowExchangeSupport.iff_eq {s t : α} (h : RowExchangeSupport I J s t)
    (a b : α) : RowExchangeSupport I J a b ↔ a = s ∧ b = t := by
  constructor
  · intro hab
    exact ⟨Finset.singleton_inj.mp (hab.1.symm.trans h.1),
      Finset.singleton_inj.mp (hab.2.1.symm.trans h.2.1)⟩
  · rintro ⟨rfl, rfl⟩
    exact h

theorem RaisingSupport.not_lowering {s : α} {t : β} (h : RaisingSupport I J s t)
    (a : α) (b : β) : ¬ LoweringSupport I J a b := by
  intro hab
  exact Finset.empty_ne_singleton a (h.1.symm.trans hab.1)

theorem RaisingSupport.not_columnExchange {s : α} {t : β}
    (h : RaisingSupport I J s t) (a b : β) : ¬ ColumnExchangeSupport I J a b := by
  intro hab
  exact Finset.singleton_ne_empty s (h.2.1.symm.trans hab.2.1)

theorem RaisingSupport.not_rowExchange {s : α} {t : β}
    (h : RaisingSupport I J s t) (a b : α) : ¬ RowExchangeSupport I J a b := by
  intro hab
  exact Finset.empty_ne_singleton a (h.1.symm.trans hab.1)

theorem LoweringSupport.not_columnExchange {s : α} {t : β}
    (h : LoweringSupport I J s t) (a b : β) : ¬ ColumnExchangeSupport I J a b := by
  intro hab
  exact Finset.singleton_ne_empty s (h.1.symm.trans hab.1)

theorem LoweringSupport.not_rowExchange {s : α} {t : β}
    (h : LoweringSupport I J s t) (a b : α) : ¬ RowExchangeSupport I J a b := by
  intro hab
  exact Finset.singleton_ne_empty t (h.2.2.1.symm.trans hab.2.2.1)

theorem ColumnExchangeSupport.not_rowExchange {s t : β}
    (h : ColumnExchangeSupport I J s t) (a b : α) : ¬ RowExchangeSupport I J a b := by
  intro hab
  exact Finset.empty_ne_singleton a (h.1.symm.trans hab.1)

end Support

/-- A unique support pair leaves exactly one term in the double sum. -/
private theorem sum_sum_ite_of_unique_support [Fintype α] [Fintype β]
    (P : α → β → Prop) (f : α → β → ℤ) (s : α) (t : β)
    (h : ∀ a b, P a b ↔ a = s ∧ b = t) :
    (∑ a, ∑ b, if P a b then f a b else 0) = f s t := by
  let := Classical.propDecidable
  calc
    (∑ a, ∑ b, if P a b then f a b else 0) =
        ∑ b, if P s b then f s b else 0 := by
      refine Finset.sum_eq_single_of_mem s (Finset.mem_univ s) ?_
      intro a _ hne
      refine Finset.sum_eq_zero ?_
      intro b _
      exact if_neg (fun hab => hne ((h a b).mp hab).1)
    _ = (if P s t then f s t else 0) := by
      refine Finset.sum_eq_single_of_mem t (Finset.mem_univ t) ?_
      intro b _ hne
      exact if_neg (fun hsb => hne ((h s b).mp hsb).2)
    _ = f s t := if_pos ((h s t).mpr ⟨rfl, rfl⟩)

section Coefficients
variable [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
variable {I J : MinorIndex α β}

-- An explicit decision family preserves the frozen support instances; the
-- `classical` tactic would instead register that family at low priority.
theorem raisingCoefficient_of_support {s : α} {t : β} (h : RaisingSupport I J s t) :
    raisingCoefficient I J = (-1 : ℤ) ^ (position s J.1.1 + position t J.1.2) := by
  let := Classical.propDecidable
  exact sum_sum_ite_of_unique_support (RaisingSupport I J)
    (fun a b => (-1 : ℤ) ^ (position a J.1.1 + position b J.1.2)) s t h.iff_eq

theorem loweringCoefficient_of_support {s : α} {t : β} (h : LoweringSupport I J s t) :
    loweringCoefficient I J = (-1 : ℤ) ^ (position s I.1.1 + position t I.1.2) := by
  let := Classical.propDecidable
  exact sum_sum_ite_of_unique_support (LoweringSupport I J)
    (fun a b => (-1 : ℤ) ^ (position a I.1.1 + position b I.1.2)) s t h.iff_eq

omit [Fintype α] [LinearOrder α] in
theorem columnExchangeCoefficient_of_support {s t : β}
    (h : ColumnExchangeSupport I J s t) :
    columnExchangeCoefficient I J =
      (-1 : ℤ) ^ (position s I.1.2 + position t J.1.2) := by
  let := Classical.propDecidable
  exact sum_sum_ite_of_unique_support (ColumnExchangeSupport I J)
    (fun a b => (-1 : ℤ) ^ (position a I.1.2 + position b J.1.2)) s t h.iff_eq

omit [Fintype β] [LinearOrder β] in
theorem rowExchangeCoefficient_of_support {s t : α} (h : RowExchangeSupport I J s t) :
    rowExchangeCoefficient I J = (-1 : ℤ) ^ (position s I.1.1 + position t J.1.1) := by
  let := Classical.propDecidable
  exact sum_sum_ite_of_unique_support (RowExchangeSupport I J)
    (fun a b => (-1 : ℤ) ^ (position a I.1.1 + position b J.1.1)) s t h.iff_eq

theorem raisingCoefficient_zero (h : ∀ s t, ¬ RaisingSupport I J s t) :
    raisingCoefficient I J = 0 := by
  let := Classical.propDecidable
  simp [raisingCoefficient, h]

theorem loweringCoefficient_zero (h : ∀ s t, ¬ LoweringSupport I J s t) :
    loweringCoefficient I J = 0 := by
  let := Classical.propDecidable
  simp [loweringCoefficient, h]

omit [Fintype α] [LinearOrder α] in
theorem columnExchangeCoefficient_zero (h : ∀ s t, ¬ ColumnExchangeSupport I J s t) :
    columnExchangeCoefficient I J = 0 := by
  let := Classical.propDecidable
  simp [columnExchangeCoefficient, h]

omit [Fintype β] [LinearOrder β] in
theorem rowExchangeCoefficient_zero (h : ∀ s t, ¬ RowExchangeSupport I J s t) :
    rowExchangeCoefficient I J = 0 := by
  let := Classical.propDecidable
  simp [rowExchangeCoefficient, h]

end Coefficients
end NLA.NM04

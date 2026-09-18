/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The canonical integer matrix: diagonal, all four signed off-diagonal cases, and zero.
-/
import NLA.NM04.DecisionTransport
import LeanCert.Tactic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04

-- Match the frozen definitions and Challenge decision instances.
attribute [local instance] Classical.propDecidable

theorem H_diagonal (m n : ℕ) (I : Index m n) :
    H m n I I = (I.1.1.card : ℤ) * ((m : ℤ) + (n : ℤ)) - (m : ℤ) * (n : ℤ) := by
  simp [H]

theorem H_raising (m n : ℕ) (I J : Index m n) (hIJ : I ≠ J)
    (s : Tail m) (t : Tail n) (h : RaisingSupport I J s t) :
    H m n I J = (-1 : ℤ) ^ (position s J.1.1 + position t J.1.2) * (m : ℤ) := by
  -- Freeze the existing finite enumerations before aligning equality decisions.
  let tailFintypeM : Fintype (Tail m) := inferInstance
  let tailFintypeN : Fintype (Tail n) := inferInstance
  let := Classical.propDecidable
  have hc : @RaisingSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => @RaisingSupport (Tail m) (Tail n) da db I J s t) h
  have hU := raisingCoefficient_of_support hc
  have hL := loweringCoefficient_zero hc.not_lowering
  have hC := column_coefficient_all_decisions I J 0
    (columnExchangeCoefficient_zero hc.not_columnExchange)
  have hR := row_coefficient_all_decisions I J 0
    (rowExchangeCoefficient_zero hc.not_rowExchange)
  simp [H, hIJ, hU, hL, hC, hR, mul_comm]

theorem H_lowering (m n : ℕ) (I J : Index m n) (hIJ : I ≠ J)
    (s : Tail m) (t : Tail n) (h : LoweringSupport I J s t) :
    H m n I J = (-1 : ℤ) ^ (position s I.1.1 + position t I.1.2 + 1) * (n : ℤ) := by
  -- Freeze the existing finite enumerations before aligning equality decisions.
  let tailFintypeM : Fintype (Tail m) := inferInstance
  let tailFintypeN : Fintype (Tail n) := inferInstance
  let := Classical.propDecidable
  have hc : @LoweringSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => @LoweringSupport (Tail m) (Tail n) da db I J s t) h
  have hU := raisingCoefficient_zero (fun a b ha => ha.not_lowering s t hc)
  have hL := loweringCoefficient_of_support hc
  have hC := column_coefficient_all_decisions I J 0
    (columnExchangeCoefficient_zero hc.not_columnExchange)
  have hR := row_coefficient_all_decisions I J 0
    (rowExchangeCoefficient_zero hc.not_rowExchange)
  simp only [H, if_neg hIJ, hU, hL, hC, hR, mul_zero, zero_sub, add_zero, pow_succ]
  ring

theorem H_column_exchange (m n : ℕ) (I J : Index m n) (hIJ : I ≠ J)
    (s t : Tail n) (h : ColumnExchangeSupport I J s t) :
    H m n I J = (-1 : ℤ) ^ (position s I.1.2 + position t J.1.2) * (m : ℤ) := by
  -- Freeze the existing finite enumerations before aligning equality decisions.
  let tailFintypeM : Fintype (Tail m) := inferInstance
  let tailFintypeN : Fintype (Tail n) := inferInstance
  let := Classical.propDecidable
  have hc : @ColumnExchangeSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => @ColumnExchangeSupport (Tail m) (Tail n) da db I J s t) h
  have hU := raisingCoefficient_zero (fun a b ha => ha.not_columnExchange s t hc)
  have hL := loweringCoefficient_zero (fun a b ha => ha.not_columnExchange s t hc)
  have hC := column_coefficient_all_decisions I J _
    (columnExchangeCoefficient_of_support hc)
  have hR := row_coefficient_all_decisions I J 0
    (rowExchangeCoefficient_zero hc.not_rowExchange)
  simp [H, hIJ, hU, hL, hC, hR, mul_comm]

theorem H_row_exchange (m n : ℕ) (I J : Index m n) (hIJ : I ≠ J)
    (s t : Tail m) (h : RowExchangeSupport I J s t) :
    H m n I J = (-1 : ℤ) ^ (position s I.1.1 + position t J.1.1) * (n : ℤ) := by
  -- Freeze the existing finite enumerations before aligning equality decisions.
  let tailFintypeM : Fintype (Tail m) := inferInstance
  let tailFintypeN : Fintype (Tail n) := inferInstance
  let := Classical.propDecidable
  have hc : @RowExchangeSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => @RowExchangeSupport (Tail m) (Tail n) da db I J s t) h
  have hU := raisingCoefficient_zero (fun a b ha => ha.not_rowExchange s t hc)
  have hL := loweringCoefficient_zero (fun a b ha => ha.not_rowExchange s t hc)
  have hC := column_coefficient_all_decisions I J 0
    (columnExchangeCoefficient_zero (fun a b ha => ha.not_rowExchange s t hc))
  have hR := row_coefficient_all_decisions I J _
    (rowExchangeCoefficient_of_support hc)
  simp [H, hIJ, hU, hL, hC, hR, mul_comm]

theorem H_other (m n : ℕ) (I J : Index m n) (hIJ : I ≠ J)
    (hU : ¬ ∃ (s : Tail m) (t : Tail n), RaisingSupport I J s t)
    (hL : ¬ ∃ (s : Tail m) (t : Tail n), LoweringSupport I J s t)
    (hC : ¬ ∃ s t : Tail n, ColumnExchangeSupport I J s t)
    (hR : ¬ ∃ s t : Tail m, RowExchangeSupport I J s t) : H m n I J = 0 := by
  -- Freeze the existing finite enumerations before aligning equality decisions.
  let tailFintypeM : Fintype (Tail m) := inferInstance
  let tailFintypeN : Fintype (Tail n) := inferInstance
  let := Classical.propDecidable
  have hUc : ¬ ∃ (s : Tail m) (t : Tail n), @RaisingSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => ¬ ∃ (s : Tail m) (t : Tail n), @RaisingSupport (Tail m) (Tail n) da db I J s t) hU
  have hLc : ¬ ∃ (s : Tail m) (t : Tail n), @LoweringSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => ¬ ∃ (s : Tail m) (t : Tail n), @LoweringSupport (Tail m) (Tail n) da db I J s t) hL
  have hCc : ¬ ∃ s t : Tail n, @ColumnExchangeSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => ¬ ∃ s t : Tail n, @ColumnExchangeSupport (Tail m) (Tail n) da db I J s t) hC
  have hRc : ¬ ∃ s t : Tail m, @RowExchangeSupport (Tail m) (Tail n)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) I J s t :=
    support_decision_transport
      (fun da db => ¬ ∃ s t : Tail m, @RowExchangeSupport (Tail m) (Tail n) da db I J s t) hR
  have hU0 := raisingCoefficient_zero (fun a b h => hUc ⟨a, b, h⟩)
  have hL0 := loweringCoefficient_zero (fun a b h => hLc ⟨a, b, h⟩)
  have hC0 := column_coefficient_all_decisions I J 0
    (columnExchangeCoefficient_zero (fun a b h => hCc ⟨a, b, h⟩))
  have hR0 := row_coefficient_all_decisions I J 0
    (rowExchangeCoefficient_zero (fun a b h => hRc ⟨a, b, h⟩))
  simp [H, hIJ, hU0, hL0, hC0, hR0]

#print axioms H_diagonal
#assert_trust kernel H_diagonal
#print axioms H_raising
#assert_trust kernel H_raising
#print axioms H_lowering
#assert_trust kernel H_lowering
#print axioms H_column_exchange
#assert_trust kernel H_column_exchange
#print axioms H_row_exchange
#assert_trust kernel H_row_exchange
#print axioms H_other
#assert_trust kernel H_other

end NLA.NM04

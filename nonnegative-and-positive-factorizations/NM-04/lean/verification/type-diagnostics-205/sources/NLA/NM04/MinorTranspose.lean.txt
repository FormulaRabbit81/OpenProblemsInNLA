/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

Transpose transports for the actual ordered minors and cofactor forms.
-/
import NLA.NM04.CofactorSigned
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

/-- Swap the actual selected row and column sets. -/
def minorTransposeIndex {α : Type u} {β : Type v} (I : MinorIndex α β) :
    MinorIndex β α := ⟨(I.1.2, I.1.1), I.property.symm⟩

def minorTransposeEquiv (α : Type u) (β : Type v) : MinorIndex α β ≃ MinorIndex β α where
  toFun := minorTransposeIndex
  invFun := minorTransposeIndex
  left_inv I := by apply Subtype.ext; rfl
  right_inv I := by apply Subtype.ext; rfl

/-- The increasing row/column enumerations swap without a permutation sign. -/
theorem minor_transpose {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    minor Tᵀ (minorTransposeIndex I) = minor T I := by
  calc
    _ = (minorMatrix T I)ᵀ.det :=
      minor_ordered_det Tᵀ (minorTransposeIndex I) I.property.symm
    _ = minor T I := Matrix.det_transpose (minorMatrix T I)

/-- C20 shows transpose invariance of the actual cofactor form, including order
zero. Its erased index transposes by the literal swap of its two sets. -/
theorem cofactorForm_transpose {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) (Z : Matrix α β 𝕜) :
    cofactorForm Tᵀ (minorTransposeIndex I) Zᵀ = cofactorForm T I Z := by
  calc
    _ = ∑ t : I.1.2, ∑ s : I.1.1,
        (-1 : 𝕜) ^ (position (t : β) I.1.2 + position (s : α) I.1.1) *
          Z s t * minor Tᵀ (erasedIndex (minorTransposeIndex I) t s) :=
      cofactor_signed_minor_formula Tᵀ Zᵀ (minorTransposeIndex I)
    _ = ∑ s : I.1.1, ∑ t : I.1.2,
        (-1 : 𝕜) ^ (position (t : β) I.1.2 + position (s : α) I.1.1) *
          Z s t * minor Tᵀ (erasedIndex (minorTransposeIndex I) t s) :=
      Finset.sum_comm
    _ = ∑ s : I.1.1, ∑ t : I.1.2,
        (-1 : 𝕜) ^ (position (s : α) I.1.1 + position (t : β) I.1.2) *
          Z s t * minor T (erasedIndex I s t) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      have hm : minor Tᵀ (erasedIndex (minorTransposeIndex I) t s) =
          minor T (erasedIndex I s t) := minor_transpose T (erasedIndex I s t)
      rw [hm, Nat.add_comm]
    _ = _ := (cofactor_signed_minor_formula T Z I).symm

theorem columnExchangeCoefficient_transpose {α : Type u} {β : Type v}
    [Fintype α] [LinearOrder α] [DecidableEq β] (I J : MinorIndex α β) :
    columnExchangeCoefficient (minorTransposeIndex I) (minorTransposeIndex J) =
      rowExchangeCoefficient I J := by
  unfold columnExchangeCoefficient rowExchangeCoefficient
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have hs : ColumnExchangeSupport (minorTransposeIndex I) (minorTransposeIndex J) s t ↔
      RowExchangeSupport I J s t :=
    ⟨fun h => ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩,
      fun h => ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩⟩
  change (if ColumnExchangeSupport (minorTransposeIndex I) (minorTransposeIndex J) s t then
      (-1 : ℤ) ^ (position s I.1.1 + position t J.1.1) else 0) =
    (if RowExchangeSupport I J s t then
      (-1 : ℤ) ^ (position s I.1.1 + position t J.1.1) else 0)
  simp only [hs]

/-- Reindex all minor indices by the set-swap equivalence. -/
theorem columnExchange_transpose {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    columnExchange (minor Tᵀ) (minorTransposeIndex I) = rowExchange (minor T) I := by
  unfold columnExchange rowExchange
  symm
  refine Fintype.sum_equiv (minorTransposeEquiv α β) _ _ ?_
  intro J
  exact congrArg₂ (· * ·)
    (congrArg (fun z : ℤ => (z : 𝕜)) (columnExchangeCoefficient_transpose I J).symm)
    (minor_transpose T J).symm

#print axioms minor_transpose
#assert_trust kernel minor_transpose
#print axioms cofactorForm_transpose
#assert_trust kernel cofactorForm_transpose
#print axioms columnExchangeCoefficient_transpose
#assert_trust kernel columnExchangeCoefficient_transpose
#print axioms columnExchange_transpose
#assert_trust kernel columnExchange_transpose

end
end NLA.NM04

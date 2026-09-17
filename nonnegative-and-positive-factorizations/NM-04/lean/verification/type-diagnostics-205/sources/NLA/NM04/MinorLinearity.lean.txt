/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Elementary linearity of the actual
cofactor form and finite transition operators used in Colbrook's NM-04 proof.
-/
import NLA.NM04.Definitions
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w z

section Cofactor
variable {α : Type u} {β : Type v} {𝕜 : Type w}
variable [LinearOrder α] [LinearOrder β] [CommRing 𝕜]

theorem cofactorForm_zero (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I 0 = 0 := by
  simp [cofactorForm, minorMatrix]

theorem cofactorForm_add (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (U V : Matrix α β 𝕜) :
    cofactorForm T I (U + V) = cofactorForm T I U + cofactorForm T I V := by
  simp only [cofactorForm, minorMatrix, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem cofactorForm_smul (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (a : 𝕜) (Z : Matrix α β 𝕜) :
    cofactorForm T I (a • Z) = a * cofactorForm T I Z := by
  unfold cofactorForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [minorMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

theorem cofactorForm_sum {D : Type z} [DecidableEq D]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) (E : Finset D)
    (Z : D → Matrix α β 𝕜) :
    cofactorForm T I (∑ d ∈ E, Z d) = ∑ d ∈ E, cofactorForm T I (Z d) := by
  induction E using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cofactorForm_zero]
  | @insert d E hd ih =>
    simp only [Finset.sum_insert hd, cofactorForm_add, ih]

end Cofactor

section Transitions
variable {α : Type u} {β : Type v} {𝕜 : Type w}
variable [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]

omit [LinearOrder α] [LinearOrder β] in
private theorem coefficient_sum_smul (c : MinorIndex α β → ℤ)
    (f : MinorIndex α β → 𝕜) (a : 𝕜) :
    (∑ J, (c J : 𝕜) * (a * f J)) = a * ∑ J, (c J : 𝕜) * f J := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem raising_smul (f : MinorIndex α β → 𝕜) (a : 𝕜) (I : MinorIndex α β) :
    raising (fun J => a * f J) I = a * raising f I :=
  coefficient_sum_smul (raisingCoefficient I) f a

theorem lowering_smul (f : MinorIndex α β → 𝕜) (a : 𝕜) (I : MinorIndex α β) :
    lowering (fun J => a * f J) I = a * lowering f I :=
  coefficient_sum_smul (loweringCoefficient I) f a

omit [LinearOrder α] in
theorem columnExchange_smul [DecidableEq α]
    (f : MinorIndex α β → 𝕜) (a : 𝕜) (I : MinorIndex α β) :
    columnExchange (fun J => a * f J) I = a * columnExchange f I :=
  coefficient_sum_smul (columnExchangeCoefficient I) f a

omit [LinearOrder β] in
theorem rowExchange_smul [DecidableEq β]
    (f : MinorIndex α β → 𝕜) (a : 𝕜) (I : MinorIndex α β) :
    rowExchange (fun J => a * f J) I = a * rowExchange f I :=
  coefficient_sum_smul (rowExchangeCoefficient I) f a

end Transitions

#print axioms cofactorForm_zero
#print axioms cofactorForm_add
#print axioms cofactorForm_smul
#print axioms cofactorForm_sum
#print axioms raising_smul
#print axioms lowering_smul
#print axioms columnExchange_smul
#print axioms rowExchange_smul
#assert_trust kernel cofactorForm_zero
#assert_trust kernel cofactorForm_add
#assert_trust kernel cofactorForm_smul
#assert_trust kernel cofactorForm_sum
#assert_trust kernel raising_smul
#assert_trust kernel lowering_smul
#assert_trust kernel columnExchange_smul
#assert_trust kernel rowExchange_smul

end
end NLA.NM04

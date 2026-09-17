/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

The frozen roots are the actual CFC.sqrt values. Mathlib supplies their
nonnegativity and square identities. Invertibility follows from the proved
positive-definite inputs and the existing noncommutative unit-square lemma.
-/
import NLA.SP15.ParameterPositivity
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

theorem square_root_semantics (x : Parameters) (hx : x ∈ parameterBox) :
    (pRoot x).IsHermitian ∧ (qRoot x).IsHermitian ∧
    pRoot x * pRoot x = pMatrix x ∧ qRoot x * qRoot x = qMatrix x ∧
    IsUnit (pRoot x) ∧ IsUnit (qRoot x) := by
  obtain ⟨hP, hQ⟩ := parameter_matrices_positive x hx
  have hPnonneg : (0 : Square 3) ≤ pMatrix x := hP.posSemidef.nonneg
  have hQnonneg : (0 : Square 3) ≤ qMatrix x := hQ.posSemidef.nonneg
  have hproot : (0 : Square 3) ≤ pRoot x := by
    simpa only [pRoot] using CFC.sqrt_nonneg (pMatrix x)
  have hqroot : (0 : Square 3) ≤ qRoot x := by
    simpa only [qRoot] using CFC.sqrt_nonneg (qMatrix x)
  have hpsquare : pRoot x * pRoot x = pMatrix x := by
    simpa only [pRoot] using CFC.sqrt_mul_sqrt_self (pMatrix x) hPnonneg
  have hqsquare : qRoot x * qRoot x = qMatrix x := by
    simpa only [qRoot] using CFC.sqrt_mul_sqrt_self (qMatrix x) hQnonneg
  refine ⟨(Matrix.nonneg_iff_posSemidef.mp hproot).isHermitian,
    (Matrix.nonneg_iff_posSemidef.mp hqroot).isHermitian, hpsquare, hqsquare, ?_, ?_⟩
  · apply isUnit_mul_self_iff.mp
    rw [hpsquare]
    exact hP.isUnit
  · apply isUnit_mul_self_iff.mp
    rw [hqsquare]
    exact hQ.isUnit

#print axioms square_root_semantics
#assert_trust kernel square_root_semantics

end
end NLA.SP15

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md.

Polynomial intertwining preserves multiplication order. Both norm inequalities
use the actual reversal isometry, so the zero-dimensional case is included.
-/
import NLA.IE02.JordanReversal
import NLA.IE02.SchurEnergy

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open Polynomial

private theorem polynomial_intertwine {n : ℕ} (A B R : Square n)
    (h : A * R = R * B) (p : Poly) : polyEval p A * R = R * polyEval p B := by
  unfold polyEval
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial k c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.mul_smul, one_mul]
    rw [(SemiconjBy.pow_right (a := R) (x := B) (y := A) h.symm k).eq.symm]

private theorem reversal_intertwining_norm {n : ℕ} (A B : Square n)
    (h : ∀ x : H n, euclideanLin A (reverseVector x) =
      reverseVector (euclideanLin B x)) : operatorNorm A = operatorNorm B := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (euclideanCLM A)
      (norm_nonneg (euclideanCLM B))
    intro x
    have hx := h (reverseVector x)
    rw [reverseVector_involutive] at hx
    calc
      ‖euclideanLin A x‖ = ‖euclideanLin B (reverseVector x)‖ := by
        rw [hx, reverseVector_norm]
      _ ≤ operatorNorm B * ‖reverseVector x‖ := (euclideanCLM B).le_opNorm _
      _ = operatorNorm B * ‖x‖ := by rw [reverseVector_norm]
  · apply ContinuousLinearMap.opNorm_le_bound (euclideanCLM B)
      (norm_nonneg (euclideanCLM A))
    intro x
    calc
      ‖euclideanLin B x‖ = ‖euclideanLin A (reverseVector x)‖ := by
        rw [h x, reverseVector_norm]
      _ ≤ operatorNorm A * ‖reverseVector x‖ := (euclideanCLM A).le_opNorm _
      _ = operatorNorm A * ‖x‖ := by rw [reverseVector_norm]

theorem jordan_polynomial_transport (n : ℕ) (lam : ℂ) (p : Poly) :
    polyEval p (jordan n lam) * reversal n = reversal n * polyEval p (lowerJordan n lam) ∧
    operatorNorm (polyEval p (jordan n lam)) = operatorNorm (polyEval p (lowerJordan n lam)) ∧
    (∀ x : H n, euclideanLin (polyEval p (jordan n lam)) (reverseVector x) =
      reverseVector (euclideanLin (polyEval p (lowerJordan n lam)) x)) := by
  obtain ⟨hstar, hsquare, hconj, _⟩ := jordan_reversal n lam
  rw [hstar] at hconj
  have hbase : jordan n lam * reversal n = reversal n * lowerJordan n lam := by
    calc
      jordan n lam * reversal n =
          (reversal n * reversal n) * jordan n lam * reversal n := by rw [hsquare, one_mul]
      _ = reversal n * (reversal n * jordan n lam * reversal n) := by
        simp only [mul_assoc]
      _ = reversal n * lowerJordan n lam := by rw [hconj]
  have hpoly := polynomial_intertwine _ _ _ hbase p
  have hvec (x : H n) : euclideanLin (polyEval p (jordan n lam)) (reverseVector x) =
      reverseVector (euclideanLin (polyEval p (lowerJordan n lam)) x) := by
    have hx := congrArg (fun M : Square n => euclideanLin M x) hpoly
    simpa only [euclideanLin_mul_apply, reversal_action] using hx
  exact ⟨hpoly, reversal_intertwining_norm _ _ hvec, hvec⟩

#print axioms jordan_polynomial_transport
#assert_trust kernel jordan_polynomial_transport

end
end NLA.IE02

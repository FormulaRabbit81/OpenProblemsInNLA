/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's polynomial algebra evaluation, finite coefficient expansion,
degree estimates, and finite-sum reindexing.

Normalized complex polynomials give exactly the finite affine power residuals.
No independence of matrix powers, nonzero dimension, or positive degree is assumed.
-/
import NLA.IE02.Definitions
import Mathlib.Algebra.BigOperators.Fin
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators
open Polynomial

/-- The normalization fixes only the constant term; all remaining coefficients are complex. -/
theorem polynomial_residual_parameterization {n : ℕ} (A : Square n) (k : ℕ) :
    (∀ p : Poly, Admissible k p → ∃ c : Fin k → ℂ,
      polyEval p A = affineResidual 1 (fun j : Fin k => A ^ (j.val + 1)) c) ∧
    (∀ c : Fin k → ℂ, ∃ p : Poly, Admissible k p ∧
      polyEval p A = affineResidual 1 (fun j : Fin k => A ^ (j.val + 1)) c) := by
  constructor
  · intro p hp
    have hdegree : p.natDegree < k + 1 :=
      Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hp.1)
    have hzero : p.coeff 0 = 1 := (Polynomial.coeff_zero_eq_eval_zero p).trans hp.2
    have hexpansion : polyEval p A =
        1 + ∑ j : Fin k, p.coeff (j.val + 1) • A ^ (j.val + 1) := by
      rw [polyEval, Polynomial.aeval_eq_sum_range' hdegree A,
        ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, pow_zero, hzero, one_smul]
    refine ⟨fun j => -p.coeff (j.val + 1), ?_⟩
    rw [hexpansion]
    simp only [affineResidual, directionSum, neg_smul, Finset.sum_neg_distrib,
      sub_neg_eq_add]
  · intro c
    let p : Poly := 1 - ∑ j : Fin k, C (c j) * X ^ (j.val + 1)
    have hterm (j : Fin k) : DegreeLE (C (c j) * (X : Poly) ^ (j.val + 1)) k :=
      Polynomial.degree_le_of_natDegree_le
        ((Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.succ_le_of_lt j.is_lt))
    have hsum : DegreeLE (∑ j : Fin k, C (c j) * (X : Poly) ^ (j.val + 1)) k :=
      (Polynomial.degree_sum_le Finset.univ _).trans
        (Finset.sup_le fun j _hj => hterm j)
    have hone : DegreeLE (1 : Poly) k :=
      Polynomial.degree_le_of_natDegree_le (by simp)
    have hp : Admissible k p := by
      constructor
      · exact (Polynomial.degree_sub_le _ _).trans (max_le hone hsum)
      · simp [p, Polynomial.eval_finsetSum]
    refine ⟨p, hp, ?_⟩
    -- Algebra evaluation sends each positive power to the corresponding matrix power.
    simp only [polyEval, p, map_sub, map_one, map_sum, map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, affineResidual, directionSum]

/-- The two witness directions identify value sets before any extremum is taken. -/
theorem polynomial_residual_value_set {n : ℕ} {α : Type*} (A : Square n) (k : ℕ)
    (f : Square n → α) :
    {t : α | ∃ p : Poly, Admissible k p ∧ t = f (polyEval p A)} =
      Set.range (fun c : Fin k → ℂ =>
        f (affineResidual 1 (fun j : Fin k => A ^ (j.val + 1)) c)) := by
  ext t
  constructor
  · rintro ⟨p, hp, ht⟩
    obtain ⟨c, hc⟩ := (polynomial_residual_parameterization A k).1 p hp
    exact ⟨c, (congrArg f hc).symm.trans ht.symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨p, hp, heval⟩ := (polynomial_residual_parameterization A k).2 c
    exact ⟨p, hp, (congrArg f heval).symm⟩

theorem normalized_polynomial_residuals (n k : ℕ) (lam : ℂ) :
    (∀ p : Poly, Admissible k p → ∃ c : Fin k → ℂ,
      polyEval p (lowerJordan n lam) = affineResidual 1 (jordanDirections n k lam) c) ∧
    (∀ c : Fin k → ℂ, ∃ p : Poly, Admissible k p ∧
      polyEval p (lowerJordan n lam) = affineResidual 1 (jordanDirections n k lam) c) := by
  exact polynomial_residual_parameterization (lowerJordan n lam) k

#print axioms normalized_polynomial_residuals
#assert_trust kernel normalized_polynomial_residuals

end
end NLA.IE02

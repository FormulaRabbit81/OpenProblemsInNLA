/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Homogenization uses the fixed grade N even when the original degree drops.
The leading coefficient is the actual original value p(1), not an assumed
nonzero leading coefficient of the original matrix pencil.
-/
import NLA.MF18.Definitions
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

private theorem cayley_term_degree (N j : ℕ) (hj : j ≤ N) (a : ℂ) :
    (Polynomial.C a * (Polynomial.X - 1) ^ j *
      (Polynomial.X + 1) ^ (N - j) : CPoly).natDegree ≤ N := by
  compute_degree <;> omega

private theorem cayley_term_coeff (N j : ℕ) (hj : j ≤ N) (a : ℂ) :
    (Polynomial.C a * (Polynomial.X - 1) ^ j *
      (Polynomial.X + 1) ^ (N - j) : CPoly).coeff N = a := by
  have hm : ((Polynomial.X - 1) ^ j * (Polynomial.X + 1) ^ (N - j) : CPoly).Monic := by
    monicity <;> norm_num <;> omega
  have hd : ((Polynomial.X - 1) ^ j * (Polynomial.X + 1) ^ (N - j) : CPoly).natDegree = N := by
    compute_degree <;> norm_num <;> omega
  have hc : ((Polynomial.X - 1) ^ j * (Polynomial.X + 1) ^ (N - j) : CPoly).coeff N = 1 := by
    exact (congrArg ((Polynomial.X - 1) ^ j *
      (Polynomial.X + 1) ^ (N - j) : CPoly).coeff hd.symm).trans hm.coeff_natDegree
  rw [mul_assoc, Polynomial.coeff_C_mul, hc, mul_one]

theorem cayley_natDegree_le (N : ℕ) (p : CPoly) : (cayleyPolynomial N p).natDegree ≤ N := by
  unfold cayleyPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact cayley_term_degree N j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (p.coeff j)

theorem cayley_coeff_grade (N : ℕ) (p : CPoly) (hd : p.natDegree ≤ N) :
    (cayleyPolynomial N p).coeff N = p.eval 1 := by
  unfold cayleyPolynomial
  rw [Polynomial.finsetSum_coeff, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [one_pow, mul_one] using
    cayley_term_coeff N j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (p.coeff j)

theorem cayley_eval (N : ℕ) (p : CPoly) (hd : p.natDegree ≤ N) (z : ℂ) (hz : z + 1 ≠ 0) :
    (cayleyPolynomial N p).eval z = (z + 1) ^ N * p.eval ((z - 1) / (z + 1)) := by
  unfold cayleyPolynomial
  rw [Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [div_pow, pow_sub₀ (z + 1) hz hjN]
  simp only [div_eq_mul_inv]
  ring

theorem monicCayley_monic_and_degree (N : ℕ) (p : CPoly)
    (hd : p.natDegree ≤ N) (h1 : p.eval 1 ≠ 0) :
    (monicCayleyPolynomial N p).Monic ∧ (monicCayleyPolynomial N p).natDegree = N := by
  have hcoeff := cayley_coeff_grade N p hd
  have hdeg : (cayleyPolynomial N p).natDegree = N :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (cayley_natDegree_le N p)
      (by rw [hcoeff]; exact h1)
  have hlead : (cayleyPolynomial N p).leadingCoeff = p.eval 1 := by
    rw [← Polynomial.coeff_natDegree, hdeg, hcoeff]
  constructor
  · -- Unfold Monic and the normalized Cayley wrapper to their leading-coefficient equality.
    change (Polynomial.C ((p.eval 1)⁻¹) * cayleyPolynomial N p).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlead, inv_mul_cancel₀ h1]
  · unfold monicCayleyPolynomial
    rw [Polynomial.natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero h1)), hdeg]

#print axioms cayley_natDegree_le
#print axioms cayley_coeff_grade
#print axioms cayley_eval
#print axioms monicCayley_monic_and_degree

end NLA.MF18

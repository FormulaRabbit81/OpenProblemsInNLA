/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root.

The scalar prefix-product-to-sum bridge uses logarithms and finite summation
by parts. It requires no eigenvalue computation, interval subdivisions or
majorization oracle. The statement is recorded before proof implementation in
SCALAR-TRANSFER-STATEMENT.md. Positivity and descending order are explicit.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.MI24

lemma weighted_prefix_sum_nonpos {n : ℕ} (w d : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : Antitone w)
    (hs : ∀ k (hk : k ≤ n), (∑ i : Fin k, d (Fin.castLE hk i)) ≤ 0) :
    (∑ i : Fin n, w i * d i) ≤ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    let c := w (Fin.last n)
    have hc : 0 ≤ c := hw _
    have hprefix :
        (∑ i : Fin n, (w i.castSucc - c) * d i.castSucc) ≤ 0 := by
      apply ih (fun i => w i.castSucc - c) (fun i => d i.castSucc)
      · intro i
        exact sub_nonneg.mpr (hm (Fin.le_last i.castSucc))
      · intro i j hij
        exact sub_le_sub_right (hm (Fin.castSucc_le_castSucc_iff.mpr hij)) c
      · intro k hk
        exact hs k (hk.trans (Nat.le_succ n))
    have htotal : (∑ i : Fin (n + 1), d i) ≤ 0 := by
      simpa only [Fin.castLE_refl] using hs (n + 1) le_rfl
    have hsplit :
        (∑ i : Fin (n + 1), w i * d i) =
        (∑ i : Fin n, (w i.castSucc - c) * d i.castSucc) +
          c * ∑ i : Fin (n + 1), d i := by
      rw [Fin.sum_univ_castSucc (fun i => w i * d i),
        Fin.sum_univ_castSucc d]
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      dsimp [c]
      ring
    rw [hsplit]
    exact add_nonpos hprefix (mul_nonpos_of_nonneg_of_nonpos hc htotal)

lemma positive_difference_le_log_tangent {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * (Real.log a - Real.log b) := by
  have ht := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
  have hdiv : a * (b / a) = b := by field_simp
  simp only [Real.log_div hb.ne' ha.ne', mul_sub, hdiv, mul_one] at ht
  nlinarith

/-- Positive descending prefix-product domination implies sum domination.
The target vector need not itself be sorted. Empty finite vectors are allowed. -/
theorem sum_le_sum_of_prefix_prod_le {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hsort : Antitone a)
    (hprod : ∀ k (hk : k ≤ n),
      (∏ i : Fin k, a (Fin.castLE hk i)) ≤
        (∏ i : Fin k, b (Fin.castLE hk i))) :
    (∑ i : Fin n, a i) ≤ ∑ i : Fin n, b i := by
  have hlogs : ∀ k (hk : k ≤ n),
      (∑ i : Fin k, (Real.log (a (Fin.castLE hk i)) -
        Real.log (b (Fin.castLE hk i)))) ≤ 0 := by
    intro k hk
    have hlog := Real.log_le_log
      (Finset.prod_pos (fun i _ => ha (Fin.castLE hk i))) (hprod k hk)
    rw [Real.log_prod (fun i _ => (ha (Fin.castLE hk i)).ne'),
      Real.log_prod (fun i _ => (hb (Fin.castLE hk i)).ne')] at hlog
    rw [Finset.sum_sub_distrib]
    exact sub_nonpos.mpr hlog
  have hweighted := weighted_prefix_sum_nonpos a
    (fun i => Real.log (a i) - Real.log (b i)) (fun i => (ha i).le) hsort hlogs
  have hsum : (∑ i : Fin n, (a i - b i)) ≤
      ∑ i : Fin n, a i * (Real.log (a i) - Real.log (b i)) :=
    Finset.sum_le_sum (fun i _ => positive_difference_le_log_tangent (ha i) (hb i))
  exact sub_nonpos.mp (by simpa only [Finset.sum_sub_distrib] using hsum.trans hweighted)

#print axioms sum_le_sum_of_prefix_prod_le
end NLA.MI24

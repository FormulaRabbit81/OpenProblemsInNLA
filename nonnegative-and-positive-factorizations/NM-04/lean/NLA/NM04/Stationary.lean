/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain the original
question; Matthew J. Colbrook retains the complete coefficient-identity proof.

The actual column imbalance has coordinate sum zero. It is therefore a
permitted direction in the zero-sum hyperplane. At a minimum, Fermat's
theorem makes the derivative along this direction zero; the proved line
derivative identifies that number as the sum of squared imbalances.
-/
import NLA.NM04.AnalyticBasics
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
open scoped BigOperators

/-- A row divided by its own positive partition has total mass one. -/
theorem row_partition_fraction_sum {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (t : Fin n → ℝ) (i : Fin m) :
    (∑ j, A i j * Real.exp (t j) / rowPartition A t i) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (row_partition_positive hn A hA t i).ne'

/-- Total column imbalance is zero because every normalized row has mass one. -/
theorem columnImbalance_sum_zero {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (t : Fin n → ℝ) :
    ∑ j, columnImbalance A t j = 0 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    zero_lt_one.trans_le (Nat.one_le_cast.mpr hn)
  have hratio : (n : ℝ) * ((m : ℝ) / (n : ℝ)) = (m : ℝ) := by
    rw [mul_comm, div_mul_cancel₀ _ hn_pos.ne']
  unfold columnImbalance
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [row_partition_fraction_sum hn A hA t]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hratio, sub_self]

/-- Any real line through zero-sum vectors remains in the zero-sum hyperplane. -/
theorem meanZero_add_smul {n : ℕ} (t d : Fin n → ℝ)
    (ht : t ∈ meanZero n) (hd : d ∈ meanZero n) (s : ℝ) :
    t + s • d ∈ meanZero n := by
  have ht_sum : ∑ j, t j = 0 := ht
  have hd_sum : ∑ j, d j = 0 := hd
  -- Unfold membership and the pointwise operations on real-valued vectors.
  change ∑ j, (t j + s * d j) = 0
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ht_sum, hd_sum, mul_zero, add_zero]

theorem potential_minimum_has_margins {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (t₀ : Fin n → ℝ) (ht₀ : t₀ ∈ meanZero n)
    (hmin : ∀ t : Fin n → ℝ, t ∈ meanZero n → potential A t₀ ≤ potential A t) :
    ∀ j : Fin n, columnImbalance A t₀ j = 0 := by
  let g : Fin n → ℝ := columnImbalance A t₀
  have hg : g ∈ meanZero n := columnImbalance_sum_zero hn A hA t₀
  have hlocal : IsLocalMin (fun s : ℝ => potential A (t₀ + s • g)) 0 := by
    have hglobal : ∀ s : ℝ,
        potential A (t₀ + (0 : ℝ) • g) ≤ potential A (t₀ + s • g) := by
      intro s
      simpa only [zero_smul, add_zero] using
        hmin (t₀ + s • g) (meanZero_add_smul t₀ g ht₀ hg s)
    exact Filter.Eventually.of_forall hglobal
  have hsquares : (∑ j, g j * g j) = 0 :=
    hlocal.hasDerivAt_eq_zero (potential_line_derivative hn A hA t₀ g)
  intro j
  have hle : g j * g j ≤ 0 := by
    calc
      g j * g j ≤ ∑ k, g k * g k :=
        Finset.single_le_sum (fun k _ => mul_self_nonneg (g k)) (Finset.mem_univ j)
      _ = 0 := hsquares
  have hzero : g j * g j = 0 := le_antisymm hle (mul_self_nonneg (g j))
  exact (mul_eq_zero.mp hzero).elim id id

#print axioms potential_minimum_has_margins
#assert_trust kernel potential_minimum_has_margins

end NLA.NM04

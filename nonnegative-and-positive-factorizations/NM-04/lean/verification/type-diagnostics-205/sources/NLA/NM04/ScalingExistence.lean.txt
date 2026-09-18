/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain the original
question; Matthew J. Colbrook retains the complete coefficient-identity proof.

Positive rectangular scaling is constructed from an actual minimum of the
log-partition potential. Exponentials give the column factors, reciprocal
positive row partitions give the row factors, and stationarity gives the
required column sums. No supplied scaling or convergence oracle is used.
-/
import NLA.NM04.Minimum
import NLA.NM04.Stationary

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
open scoped BigOperators

/-- The concrete diagonal scaling has exactly the normalized row entries. -/
theorem rowNormalized_apply {m n : ℕ} (A : Rect m n) (t : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    rowNormalized A t i j = A i j * Real.exp (t j) / rowPartition A t i := by
  simp only [rowNormalized, diagonalScale, div_eq_mul_inv]
  ring

/-- Vanishing actual column imbalance gives both required matrix margins. -/
theorem rowNormalized_balanced_of_imbalance_zero {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (t : Fin n → ℝ)
    (hzero : ∀ j, columnImbalance A t j = 0) : Balanced (rowNormalized A t) := by
  unfold Balanced
  constructor
  · intro i
    simp_rw [rowNormalized_apply]
    exact row_partition_fraction_sum hn A hA t i
  · intro j
    have hj := hzero j
    unfold columnImbalance at hj
    simpa only [rowNormalized_apply] using (sub_eq_zero.mp hj)

theorem positive_balanced_scaling_exists {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) : ∃ S : Rect m n, ScaledBalanced A S := by
  obtain ⟨t, ht, hmin⟩ := potential_attains_minimum hm hn A hA
  have hzero := potential_minimum_has_margins hn A hA t ht hmin
  refine ⟨rowNormalized A t, ?_⟩
  unfold ScaledBalanced
  refine ⟨(fun i => (rowPartition A t i)⁻¹), (fun j => Real.exp (t j)),
    ?_, ?_, rfl, ?_⟩
  · exact fun i => inv_pos.mpr (row_partition_positive hn A hA t i)
  · exact fun j => Real.exp_pos (t j)
  · exact rowNormalized_balanced_of_imbalance_zero hn A hA t hzero

#print axioms positive_balanced_scaling_exists
#assert_trust kernel positive_balanced_scaling_exists

end NLA.NM04

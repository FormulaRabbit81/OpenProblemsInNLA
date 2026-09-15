/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of Technology.
Exact elimination coordinates from the original IE-15 proof, Section 1.
Implemented with substantial OpenAI Codex assistance.
-/
import NLA.IE15.Basic

noncomputable section
open scoped BigOperators
namespace NLA.IE15

def diagPivot {n : ℕ} (A : Mat n) (k : Fin n) : ℝ :=
  trajectory A (noSwapPath n) k.val k k

def lowerMultiplier {n : ℕ} (A : Mat n) (i k : Fin n) : ℝ :=
  trajectory A (noSwapPath n) k.val i k / diagPivot A k

def upperMultiplier {n : ℕ} (A : Mat n) (k j : Fin n) : ℝ :=
  trajectory A (noSwapPath n) k.val k j / diagPivot A k

theorem diagPivot_ne_zero {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (k : Fin n) : diagPivot A k ≠ 0 :=
  (hp k).2.2.1

theorem lowerMultiplier_bound {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (i k : Fin n) (hi : k ≤ i) :
    |lowerMultiplier A i k| ≤ 1 := by
  unfold lowerMultiplier
  rw [abs_div, div_le_one (abs_pos.mpr (diagPivot_ne_zero A hp k))]
  exact (hp k).2.2.2.2 i hi

theorem upperMultiplier_bound {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (k j : Fin n) (hj : k ≤ j) :
    |upperMultiplier A k j| ≤ 1 := by
  unfold upperMultiplier
  rw [abs_div, div_le_one (abs_pos.mpr (diagPivot_ne_zero A hp k))]
  exact (hp k).2.2.2.1 j hj

theorem lowerMultiplier_mul_pivot {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (i k : Fin n) :
    lowerMultiplier A i k * diagPivot A k = trajectory A (noSwapPath n) k.val i k := by
  exact div_mul_cancel₀ _ (diagPivot_ne_zero A hp k)

theorem pivot_mul_upperMultiplier {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (k j : Fin n) :
    diagPivot A k * upperMultiplier A k j = trajectory A (noSwapPath n) k.val k j := by
  exact mul_div_cancel₀ _ (diagPivot_ne_zero A hp k)

theorem lowerMultiplier_self {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (k : Fin n) : lowerMultiplier A k k = 1 := by
  exact div_self (diagPivot_ne_zero A hp k)

theorem upperMultiplier_self {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (k : Fin n) : upperMultiplier A k k = 1 := by
  exact div_self (diagPivot_ne_zero A hp k)

theorem trajectory_next_coordinates {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (k i j : Fin n) (hi : k < i) (hj : k < j) :
    trajectory A (noSwapPath n) (k.val + 1) i j =
      trajectory A (noSwapPath n) k.val i j -
        lowerMultiplier A i k * diagPivot A k * upperMultiplier A k j := by
  rw [mul_assoc, pivot_mul_upperMultiplier A hp k j]
  simp [trajectory, k.isLt, schurStep, pivotSwap, noSwapPath, hi, hj,
    lowerMultiplier, diagPivot]

/-- A rank-one update, extended by zero beyond the matrix order. -/
def updateTerm {n : ℕ} (A : Mat n) (t : ℕ) (i j : Fin n) : ℝ :=
  if h : t < n then
    lowerMultiplier A i ⟨t,h⟩ * diagPivot A ⟨t,h⟩ * upperMultiplier A ⟨t,h⟩ j
  else 0

/-- Original entries equal their genuine Schur residual plus all preceding updates. -/
theorem entry_prefix_coordinates {n : ℕ} (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (k : ℕ) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) :
    A i j = trajectory A (noSwapPath n) k i j +
      ∑ t ∈ Finset.range k, updateTerm A t i j := by
  induction k with
  | zero => simp [trajectory]
  | succ k ih =>
    have hk : k < n := by omega
    have hi' : (⟨k,hk⟩ : Fin n) < i := hi
    have hj' : (⟨k,hk⟩ : Fin n) < j := hj
    have hprev := ih (by omega) (by omega)
    have hstep := trajectory_next_coordinates A hp ⟨k,hk⟩ i j hi' hj'
    rw [Finset.sum_range_succ]
    rw [show updateTerm A k i j =
      lowerMultiplier A i ⟨k,hk⟩ * diagPivot A ⟨k,hk⟩ * upperMultiplier A ⟨k,hk⟩ j by
        simp only [updateTerm, dif_pos hk]]
    linarith

end NLA.IE15

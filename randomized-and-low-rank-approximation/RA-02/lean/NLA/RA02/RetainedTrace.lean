/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.RA02.FutureEstimates
import NLA.RA02.StateTrace
import NLA.RA02.DistinctTrace

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma state_ordinary_diagonal_le (r : ℕ) (U : Finset (Fin r)) (i : Fin r) (hi : i ∈ U) :
    diagonalWeight r i.val * cornerValue r (U.erase i) / cornerValue r U ≤
      diagonalWeight r i.val := by
  have hc := cornerValue_erase r U i hi
  have hnonneg : 0 ≤ diagonalWeight r i.val * couplingWeight r i.val ^ 2 :=
    mul_nonneg (diagonalWeight_pos r i.val).le (sq_nonneg _)
  apply (div_le_iff₀ (cornerValue_pos r U)).2
  exact mul_le_mul_of_nonneg_left (by linarith : cornerValue r (U.erase i) ≤ cornerValue r U)
    (diagonalWeight_pos r i.val).le

lemma state_false_insert_trace_bound (r : ℕ) (F : Finset (Fin r)) (j : Fin r)
    (hj : j ∉ F) :
    realTrace (arrowheadState r (insert j F) false) ≤
      (∑ i ∈ F, diagonalWeight r i.val) + cornerValue r F / couplingWeight r j.val ^ 2 := by
  classical
  have hc : cornerValue r (insert j F) =
      cornerValue r F + diagonalWeight r j.val * couplingWeight r j.val ^ 2 := by
    simpa [hj] using cornerValue_erase r (insert j F) j (Finset.mem_insert_self j F)
  have hlow : diagonalWeight r j.val * couplingWeight r j.val ^ 2 ≤
      cornerValue r (insert j F) := by
    have hF := (cornerValue_pos r F).le
    linarith
  have hspecial : diagonalWeight r j.val * cornerValue r F / cornerValue r (insert j F) ≤
      cornerValue r F / couplingWeight r j.val ^ 2 := by
    apply (div_le_div_iff₀ (cornerValue_pos r (insert j F))
      (pow_pos (couplingWeight_pos r j.val) 2)).2
    calc
      (diagonalWeight r j.val * cornerValue r F) * couplingWeight r j.val ^ 2 =
          cornerValue r F * (diagonalWeight r j.val * couplingWeight r j.val ^ 2) := by ring
      _ ≤ cornerValue r F * cornerValue r (insert j F) :=
        mul_le_mul_of_nonneg_left hlow (cornerValue_pos r F).le
  have hsum : (∑ i ∈ F, diagonalWeight r i.val *
      cornerValue r ((insert j F).erase i) / cornerValue r (insert j F)) ≤
      ∑ i ∈ F, diagonalWeight r i.val := by
    apply Finset.sum_le_sum
    intro i hi
    exact state_ordinary_diagonal_le r (insert j F) i (Finset.mem_insert_of_mem hi)
  rw [state_false_trace, Finset.sum_insert hj]
  simp only [Finset.erase_insert hj]
  linarith

lemma state_true_future_trace_bound (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s < r) :
    realTrace (arrowheadState r (futureOrdinary r s) true) ≤
      scaleParameter r ^ s * (1 + (2 * (r : ℝ) + 1) * smallParameter r ^ 2) := by
  have hd := future_diagonal_sum_bound r hr s hs
  have hw := future_weighted_sum_bound r hr s hs
  have he := epsilon_remainder_bound r hr s hs
  rw [state_true_trace, cornerValue]
  nlinarith only [hd, hw, he]

lemma state_false_future_trace_bound (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s < r)
    (j : Fin r) (hj : j.val < s) :
    realTrace (arrowheadState r (insert j (futureOrdinary r s)) false) ≤
      scaleParameter r ^ s * (1 + (2 * (r : ℝ) + 1) * smallParameter r ^ 2) := by
  have hjF : j ∉ futureOrdinary r s := by
    intro hmem
    have hsj := (mem_futureOrdinary r s j).1 hmem
    omega
  have htrace := state_false_insert_trace_bound r (futureOrdinary r s) j hjF
  have hd := future_diagonal_sum_bound r hr s hs
  have he := exceptional_remainder_bound r hr s hs j
  have hw := future_weighted_ratio_sum_bound r hr s hs j hj
  rw [cornerValue, add_div, Finset.sum_div] at htrace
  nlinarith only [htrace, hd, he, hw]

theorem retained_trace_bound (r : ℕ) (hr : 1 ≤ r) (bits : Fin r → Bool)
    (s : ℕ) (hs : s < r) :
    0 < realTrace (pathResidual (arrowhead r) (retainedPrefix r bits s)) ∧
    realTrace (pathResidual (arrowhead r) (retainedPrefix r bits s)) ≤
      scaleParameter r ^ s * (1 + 1 / (r : ℝ)) := by
  have hsle : s ≤ r := Nat.le_of_lt hs
  refine ⟨distinct_prefix_trace_pos r hr (retainedPrefix r bits s)
    (retainedPrefix_nodup r bits s hsle) ?_, ?_⟩
  · rw [retainedPrefix_length r bits s hsle]
    exact hsle
  · have hbudget := mul_le_mul_of_nonneg_left (trace_budget_scalar_bound r hr)
      (pow_nonneg (scaleParameter_pos r).le s)
    apply le_trans ?_ hbudget
    rcases retained_carry_cases r bits s hsle with hc | ⟨j, hj, hc⟩
    · rw [retained_residual_when_last r bits s hsle hc]
      exact state_true_future_trace_bound r hr s hs
    · rw [retained_residual_when_ordinary r bits s hsle j hc]
      exact state_false_future_trace_bound r hr s hs j hj

#print axioms state_false_insert_trace_bound
#assert_trust kernel state_false_insert_trace_bound
#print axioms retained_trace_bound
#assert_trust kernel retained_trace_bound

end
end NLA.RA02

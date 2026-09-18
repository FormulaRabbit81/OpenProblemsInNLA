/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The first half-total prefix turns the geometric cross-cut bound into a
quadratic inequality. A conservative explicit bound then avoids square roots.
Every sequence length, including zero, and zero K or F are retained.
-/
import NLA.MF06.ScalarPrefixes

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06

/-- C11: all-length separated scalar sum bound, with a root-free constant. -/
theorem separated_sum_bound (n : ℕ) (x : Fin n → ℝ) (K F q : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hq0 : 0 < q) (hq1 : q < 1)
    (hx0 : ∀ i, 0 ≤ x i) (hxK : ∀ i, x i ≤ K)
    (hpair : ∀ i j : Fin n, i ≠ j →
      x i * x j ≤ F * q ^ (max i.val j.val - min i.val j.val)) :
    ∑ i : Fin n, x i ≤ 2 * K + 4 * (F * q / (1 - q) ^ 2) + 1 := by
  let X := ∑ i : Fin n, x i
  let G := F * q / (1 - q) ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg (fun i _ => hx0 i)
  have hG : 0 ≤ G := div_nonneg (mul_nonneg hF hq0.le) (sq_nonneg _)
  change X ≤ 2 * K + 4 * G + 1
  by_cases hzero : X = 0
  · rw [hzero]
    linarith
  have hpositive : 0 < X := lt_of_le_of_ne hX (fun h => hzero h.symm)
  obtain ⟨k, _hkn, hhalf0, hupper0⟩ := scalar_half_cut x K hxK hpositive
  have hhalf : X / 2 ≤ scalarPrefix x k := hhalf0
  have hupper : scalarPrefix x k ≤ X / 2 + K := hupper0
  have hprefix : 0 ≤ scalarPrefix x k := Finset.sum_nonneg (fun i _ => hx0 i)
  have hsum : scalarPrefix x k + scalarSuffix x k = X := scalarPrefix_add_suffix x k
  have hcross : scalarPrefix x k * scalarSuffix x k ≤ G :=
    scalar_cut_product_bound n x F q hF hq0 hq1 hpair k
  have hquadratic : X * (X - 2 * K) ≤ 4 * G := by
    by_cases hcase : 0 ≤ X / 2 - K
    · have hlower : X / 2 - K ≤ scalarSuffix x k := by linarith
      have hproduct : (X / 2) * (X / 2 - K) ≤ scalarPrefix x k * scalarSuffix x k :=
        mul_le_mul hhalf hlower hcase hprefix
      nlinarith
    · have hnegative : X - 2 * K ≤ 0 := by linarith
      have hproduct : X * (X - 2 * K) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hX hnegative
      linarith
  by_contra hnot
  have hbig : 2 * K + 4 * G + 1 < X := lt_of_not_ge hnot
  have hXone : 1 ≤ X := by linarith
  have hdiff : 0 ≤ X - 2 * K := by linarith
  have hproduct := mul_le_mul_of_nonneg_right hXone hdiff
  nlinarith

#print axioms separated_sum_bound
#assert_trust kernel separated_sum_bound

end NLA.MF06

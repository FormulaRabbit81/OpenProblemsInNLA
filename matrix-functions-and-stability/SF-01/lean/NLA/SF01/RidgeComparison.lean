/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Entrywise comparison of finite rational functions, including diagonal
positivity, off-diagonal domination and actual matrix nonsingularity.
-/
import NLA.SF01.WeightedRidge

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma resolvent_part_diagonal_bound {n : ℕ} (hn : 1 ≤ n) (A : Square n)
    (hA : Admissible A) (t : ℝ) (ht : 0 ≤ t) (i : Fin n) :
    (comparison A * (shifted (comparison A) t)⁻¹) i i ≤
      (A * (shifted A t)⁻¹) i i := by
  have h := resolvent_domination hn A hA t ht
  have hdiag : ((shifted A t)⁻¹) i i ≤ ((shifted (comparison A) t)⁻¹) i i :=
    (le_abs_self _).trans (h.2.2 i i)
  rw [shifted_right_resolvent (comparison A) t h.2.1,
    shifted_right_resolvent A t h.1]
  change (1 : Square n) i i - t * ((shifted (comparison A) t)⁻¹) i i ≤
    (1 : Square n) i i - t * ((shifted A t)⁻¹) i i
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hdiag ht) _

lemma resolvent_part_offDiagonal_bound {n : ℕ} (hn : 1 ≤ n) (A : Square n)
    (hA : Admissible A) (t : ℝ) (ht : 0 ≤ t) (i j : Fin n) (hij : i ≠ j) :
    |(A * (shifted A t)⁻¹) i j| ≤
      -(comparison A * (shifted (comparison A) t)⁻¹) i j := by
  have h := resolvent_domination hn A hA t ht
  rw [shifted_right_resolvent A t h.1,
    shifted_right_resolvent (comparison A) t h.2.1]
  change |(1 : Square n) i j - t * ((shifted A t)⁻¹) i j| ≤
    -((1 : Square n) i j - t * ((shifted (comparison A) t)⁻¹) i j)
  simp only [Matrix.one_apply_ne hij, zero_sub, abs_neg, abs_mul, abs_of_nonneg ht, neg_neg]
  exact mul_le_mul_of_nonneg_left (h.2.2 i j) ht

lemma weighted_abs_sum_le_neg {m : ℕ} (c u v : Fin m → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hbound : ∀ k, |u k| ≤ -v k) :
    |∑ k : Fin m, c k * u k| ≤ -(∑ k : Fin m, c k * v k) := by
  calc
    |∑ k : Fin m, c k * u k| ≤ ∑ k : Fin m, |c k * u k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin m, c k * |u k| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul, abs_of_nonneg (hc k)]
    _ ≤ ∑ k : Fin m, c k * -v k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hbound k) (hc k))
    _ = -(∑ k : Fin m, c k * v k) := by
      simp only [mul_neg, Finset.sum_neg_distrib]

lemma ridge_diagonal_bound (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) (i : Fin n) :
    ridgeEval d (comparison A) i i ≤ ridgeEval d A i i := by
  simp only [ridgeEval_apply, comparison_diagonal, abs_of_pos (hA.2 i)]
  exact add_le_add_right
    (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (resolvent_part_diagonal_bound hn A hA (d.poles k) (hd.2.2.1 k).le i)
      (hd.2.2.2 k))) _

lemma ridge_offDiagonal_bound (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A)
    (i j : Fin n) (hij : i ≠ j) :
    |ridgeEval d A i j| ≤ -ridgeEval d (comparison A) i j := by
  simp only [ridgeEval_apply, Matrix.one_apply_ne hij, mul_zero, zero_add,
    comparison_offDiagonal A i j hij]
  have hb : |d.b * A i j| = d.b * |A i j| := by
    rw [abs_mul, abs_of_pos hd.2.1]
  have hs := weighted_abs_sum_le_neg d.weights
    (fun k => (A * (shifted A (d.poles k))⁻¹) i j)
    (fun k => (comparison A * (shifted (comparison A) (d.poles k))⁻¹) i j)
    hd.2.2.2
    (fun k => resolvent_part_offDiagonal_bound hn A hA (d.poles k) (hd.2.2.1 k).le i j hij)
  calc
    |d.b * A i j + ∑ k : Fin d.size,
        d.weights k * (A * (shifted A (d.poles k))⁻¹) i j| ≤
        |d.b * A i j| + |∑ k : Fin d.size,
          d.weights k * (A * (shifted A (d.poles k))⁻¹) i j| := abs_add_le _ _
    _ ≤ d.b * |A i j| - ∑ k : Fin d.size,
        d.weights k * (comparison A * (shifted (comparison A) (d.poles k))⁻¹) i j := by
      simpa only [hb, sub_eq_add_neg] using add_le_add_right hs |d.b * A i j|
    _ = -(d.b * -|A i j| + ∑ k : Fin d.size,
        d.weights k * (comparison A * (shifted (comparison A) (d.poles k))⁻¹) i j) := by
      ring

theorem ridge_comparison_preserver (d : RidgeData) (hd : ValidData d)
    {n : ℕ} (hn : 1 ≤ n) (A : Square n) (hA : Admissible A) :
    IsZMatrix (ridgeEval d (comparison A)) ∧
    PositiveWeight (ridgeEval d (comparison A)) (weightVector (comparison A)) ∧
    (∀ i, 0 < ridgeEval d (comparison A) i i ∧
      ridgeEval d (comparison A) i i ≤ ridgeEval d A i i) ∧
    (∀ i j, i ≠ j → |ridgeEval d A i j| ≤ -ridgeEval d (comparison A) i j) ∧
    (∀ i j, ridgeEval d (comparison A) i j ≤ comparison (ridgeEval d A) i j) ∧
    Admissible (ridgeEval d A) ∧ IsUnit (ridgeEval d A) := by
  have hbase := (H_positive_weight hn A hA.1).2.1
  have hw := weightedZ_ridge d hd (comparison A) (weightVector (comparison A))
    (comparison_isZ A) hbase
  have hdiagC := weightedZ_positiveDiagonal (ridgeEval d (comparison A))
    (weightVector (comparison A)) hw.1 hw.2
  have hdiagA : PositiveDiagonal (ridgeEval d A) := by
    intro i
    exact lt_of_lt_of_le (hdiagC i) (ridge_diagonal_bound d hd hn A hA i)
  have hentry : ∀ i j,
      ridgeEval d (comparison A) i j ≤ comparison (ridgeEval d A) i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [comparison_diagonal, abs_of_pos (hdiagA i)]
      exact ridge_diagonal_bound d hd hn A hA i
    · rw [comparison_offDiagonal _ i j hij]
      have h := ridge_offDiagonal_bound d hd hn A hA i j hij
      linarith
  have hc := positiveWeight_of_entrywise_le (ridgeEval d (comparison A))
    (comparison (ridgeEval d A)) (weightVector (comparison A)) hw.2 hentry
  have hH : IsHMatrix (ridgeEval d A) :=
    weighted_Z_spectralM hn (comparison (ridgeEval d A)) (weightVector (comparison A))
      (comparison_isZ (ridgeEval d A)) hc
  refine ⟨hw.1, hw.2, ?_, ?_, hentry, ⟨hH, hdiagA⟩, ?_⟩
  · intro i
    exact ⟨hdiagC i, ridge_diagonal_bound d hd hn A hA i⟩
  · intro i j hij
    exact ridge_offDiagonal_bound d hd hn A hA i j hij
  · exact weighted_comparison_isUnit (ridgeEval d A) (weightVector (comparison A)) hc

end
end NLA.SF01

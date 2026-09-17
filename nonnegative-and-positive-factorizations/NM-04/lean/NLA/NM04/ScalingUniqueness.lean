/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain the original
question; Matthew J. Colbrook retains the complete coefficient-identity proof.

Uniqueness of positive rectangular scaling. A maximal column factor first
forces lower bounds on the row-factor products. Equality of column sums
forces equality in the maximal column; equality in one positive row then
makes every column factor the same. The factors retain their scalar gauge,
but the scaled matrix is unique.
-/
import NLA.NM04.Definitions
import LeanCert.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
open scoped BigOperators

/-- Reorder the scalar factors while retaining the concrete matrix entry. -/
theorem diagonalScale_apply {m n : ℕ} (A : Rect m n)
    (r : Fin m → ℝ) (q : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    diagonalScale A r q i j = (r i * q j) * A i j := by
  unfold diagonalScale
  ring

theorem diagonalScale_positive {m n : ℕ} (A : Rect m n) (hA : Positive A)
    (r : Fin m → ℝ) (q : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hq : ∀ j, 0 < q j) :
    Positive (diagonalScale A r q) := by
  intro i j
  exact mul_pos (mul_pos (hr i) (hA i j)) (hq j)

/-- Positivity follows from the actual factors in ScaledBalanced. -/
theorem scaledBalanced_positive {m n : ℕ} (A S : Rect m n)
    (hA : Positive A) (hS : ScaledBalanced A S) : Positive S := by
  obtain ⟨r, q, hr, hq, hS_eq, _hbalanced⟩ := hS
  rw [hS_eq]
  exact diagonalScale_positive A hA r q hr hq

/-- A second positive scaling of a positive balanced matrix can only change
the row and column factors by reciprocal scalar gauges. -/
theorem balanced_diagonalScale_factors {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (hS : Positive S) (hbalanced : Balanced S)
    (r : Fin m → ℝ) (q : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hq : ∀ j, 0 < q j)
    (hscaled : Balanced (diagonalScale S r q)) :
    ∃ c : ℝ, 0 < c ∧ (∀ i, r i * c = 1) ∧ ∀ j, q j = c := by
  classical
  obtain ⟨k, _hk, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) q
      ⟨firstIndex hn, Finset.mem_univ _⟩
  have hupper : ∀ i j, diagonalScale S r q i j ≤ (r i * q k) * S i j := by
    intro i j
    rw [diagonalScale_apply]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hr i).le) (hS i j).le
  have hrow_product : ∀ i, 1 ≤ r i * q k := by
    intro i
    calc
      1 = ∑ j, diagonalScale S r q i j := (hscaled.1 i).symm
      _ ≤ ∑ j, (r i * q k) * S i j :=
        Finset.sum_le_sum fun j _ => hupper i j
      _ = r i * q k := by
        rw [← Finset.mul_sum, hbalanced.1 i, mul_one]
  have hcolumn_lower : ∀ i, S i k ≤ diagonalScale S r q i k := by
    intro i
    rw [diagonalScale_apply]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hrow_product i) (hS i k).le
  have hcolumn_sum : (∑ i, S i k) = ∑ i, diagonalScale S r q i k :=
    (hbalanced.2 k).trans (hscaled.2 k).symm
  have hcolumn_eq : ∀ i, S i k = diagonalScale S r q i k := by
    have heq := (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ) (f := fun i : Fin m => S i k)
      (g := fun i => diagonalScale S r q i k)
      (fun i _ => hcolumn_lower i)).mp hcolumn_sum
    exact fun i => heq i (Finset.mem_univ i)
  have hproduct_eq : ∀ i, r i * q k = 1 := by
    intro i
    apply mul_right_cancel₀ (hS i k).ne'
    calc
      (r i * q k) * S i k = diagonalScale S r q i k :=
        (diagonalScale_apply S r q i k).symm
      _ = S i k := (hcolumn_eq i).symm
      _ = 1 * S i k := (one_mul _).symm
  have hentry_le : ∀ i j, diagonalScale S r q i j ≤ S i j := by
    intro i j
    calc
      diagonalScale S r q i j ≤ (r i * q k) * S i j := hupper i j
      _ = S i j := by rw [hproduct_eq i, one_mul]
  let i₀ : Fin m := firstIndex hm
  have hrow_sum : (∑ j, diagonalScale S r q i₀ j) = ∑ j, S i₀ j :=
    (hscaled.1 i₀).trans (hbalanced.1 i₀).symm
  have hrow_eq := (Finset.sum_eq_sum_iff_of_le
    (s := Finset.univ) (f := fun j : Fin n => diagonalScale S r q i₀ j)
    (g := fun j => S i₀ j) (fun j _ => hentry_le i₀ j)).mp hrow_sum
  refine ⟨q k, hq k, hproduct_eq, ?_⟩
  intro j
  have hproduct_j : r i₀ * q j = 1 := by
    apply mul_right_cancel₀ (hS i₀ j).ne'
    calc
      (r i₀ * q j) * S i₀ j = diagonalScale S r q i₀ j :=
        (diagonalScale_apply S r q i₀ j).symm
      _ = S i₀ j := hrow_eq j (Finset.mem_univ j)
      _ = 1 * S i₀ j := (one_mul _).symm
  exact mul_left_cancel₀ (hr i₀).ne' (hproduct_j.trans (hproduct_eq i₀).symm)

/-- Comparing two scalings of the same matrix uses only the nonzero original
factors. No inverse of a matrix or of one of its entries is involved. -/
theorem diagonalScale_ratio {m n : ℕ} (A : Rect m n)
    (a c : Fin m → ℝ) (b d : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    diagonalScale A c d = diagonalScale (diagonalScale A a b)
      (fun i => c i / a i) (fun j => d j / b j) := by
  funext i j
  simp only [diagonalScale]
  field_simp [ha i, hb j]

theorem positive_balanced_scaling_unique {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (S T : Rect m n)
    (hS : ScaledBalanced A S) (hT : ScaledBalanced A T) : S = T := by
  have hS_pos := scaledBalanced_positive A S hA hS
  obtain ⟨a, b, ha, hb, hS_eq, hS_balanced⟩ := hS
  obtain ⟨c, d, hc, hd, hT_eq, hT_balanced⟩ := hT
  let r : Fin m → ℝ := fun i => c i / a i
  let q : Fin n → ℝ := fun j => d j / b j
  have htransfer : T = diagonalScale S r q := by
    rw [hT_eq, hS_eq]
    exact diagonalScale_ratio A a c b d (fun i => (ha i).ne') (fun j => (hb j).ne')
  have hscaled : Balanced (diagonalScale S r q) := htransfer ▸ hT_balanced
  obtain ⟨k, _hk, hrk, hqk⟩ :=
    balanced_diagonalScale_factors hm hn S hS_pos hS_balanced r q
      (fun i => div_pos (hc i) (ha i)) (fun j => div_pos (hd j) (hb j)) hscaled
  have hmatrix : diagonalScale S r q = S := by
    funext i j
    rw [diagonalScale_apply, hqk j, hrk i, one_mul]
  exact (htransfer.trans hmatrix).symm

#print axioms positive_balanced_scaling_unique
#assert_trust kernel positive_balanced_scaling_unique

end NLA.NM04

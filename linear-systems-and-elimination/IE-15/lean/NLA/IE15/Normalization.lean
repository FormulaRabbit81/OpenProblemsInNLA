/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences,
California Institute of Technology.

The original mathematical resolution is George Stepaniants's 11 September
2026 proof. This formalization uses substantial OpenAI Codex assistance.
-/
import NLA.IE15.Basic

set_option autoImplicit false
noncomputable section
namespace NLA.IE15

/-- Choose a unit sign even when the argument vanishes. -/
def unitSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem unitSign_abs (x : ℝ) : |unitSign x| = 1 := by
  unfold unitSign
  split <;> norm_num

theorem unitSign_ne_zero (x : ℝ) : unitSign x ≠ 0 := by
  have := unitSign_abs x
  intro h
  simp [h] at this

theorem unitSign_sq (x : ℝ) : unitSign x ^ 2 = 1 := by
  unfold unitSign
  split <;> norm_num

theorem unitSign_mul (x : ℝ) : unitSign x * x = |x| := by
  unfold unitSign
  split
  next hx => simp [abs_of_nonneg hx]
  next hx => simp [abs_of_neg (lt_of_not_ge hx)]

theorem unitSign_inv (x : ℝ) : (unitSign x)⁻¹ = unitSign x := by
  unfold unitSign
  split <;> norm_num

/-- Independently rescale rows and columns and divide the whole matrix by `M`. -/
def signedScale {n : ℕ} (A : Mat n) (r c : Fin n → ℝ) (M : ℝ) : Mat n :=
  fun i j => r i * A i j * c j / M

theorem signedScale_abs {n : ℕ} (A : Mat n) (r c : Fin n → ℝ) (M : ℝ)
    (hr : ∀ i, |r i| = 1) (hc : ∀ j, |c j| = 1) (hM : 0 < M)
    (i j : Fin n) : |signedScale A r c M i j| = |A i j| / M := by
  simp only [signedScale, abs_div, abs_mul, hr, hc, one_mul, mul_one, abs_of_pos hM]

/-- Diagonal Schur complementation is covariant under nonzero diagonal scaling. -/
theorem schurStep_signedScale {n : ℕ} (S : Mat n) (r c : Fin n → ℝ) (M : ℝ)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ j, c j ≠ 0) (hM : M ≠ 0)
    (k : Fin n) (hp : S k k ≠ 0) :
    schurStep (signedScale S r c M) k k k =
      signedScale (schurStep S k k k) r c M := by
  funext i j
  simp only [schurStep, pivotSwap, Equiv.swap_self, Equiv.refl_apply, signedScale]
  by_cases hij : k < i ∧ k < j
  · simp only [if_pos hij]
    field_simp [hr k, hc k, hM, hp]
  · simp [hij]

/-- Every stage of diagonal elimination has the same signed scaling. -/
theorem trajectory_signedScale {n : ℕ} (A : Mat n) (r c : Fin n → ℝ) (M : ℝ)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ j, c j ≠ 0) (hM : M ≠ 0)
    (hp : AdmissiblePath A (noSwapPath n)) (k : ℕ) :
    trajectory (signedScale A r c M) (noSwapPath n) k =
      signedScale (trajectory A (noSwapPath n) k) r c M := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < n
    · simp only [trajectory, dif_pos hk, noSwapPath]
      rw [ih]
      apply schurStep_signedScale _ r c M hr hc hM
      exact (hp ⟨k, hk⟩).2.2.1
    · simp only [trajectory, dif_neg hk]
      funext i j
      simp [signedScale]

theorem admissiblePath_signedScale {n : ℕ} (A : Mat n) (r c : Fin n → ℝ)
    (M : ℝ) (hr : ∀ i, |r i| = 1) (hc : ∀ j, |c j| = 1) (hM : 0 < M)
    (hp : AdmissiblePath A (noSwapPath n)) :
    AdmissiblePath (signedScale A r c M) (noSwapPath n) := by
  have hr0 : ∀ i, r i ≠ 0 := by
    intro i hi
    have := hr i
    simp [hi] at this
  have hc0 : ∀ j, c j ≠ 0 := by
    intro j hj
    have := hc j
    simp [hj] at this
  intro k
  change AdmissiblePivot (trajectory (signedScale A r c M) (noSwapPath n) k.val) k k k
  rw [trajectory_signedScale A r c M hr0 hc0 hM.ne' hp]
  rcases hp k with ⟨_, _, hpiv, hrow, hcol⟩
  refine ⟨le_rfl, le_rfl, ?_, ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero (hr0 k) hpiv) (hc0 k)) hM.ne'
  · intro j hj
    simp only [signedScale_abs _ r c M hr hc hM]
    exact div_le_div_of_nonneg_right (hrow j hj) hM.le
  · intro i hi
    simp only [signedScale_abs _ r c M hr hc hM]
    exact div_le_div_of_nonneg_right (hcol i hi) hM.le

/-- Column signs and the common scale cancel from lower elimination multipliers. -/
theorem signedScale_multiplier {n : ℕ} (S : Mat n) (r c : Fin n → ℝ) (M : ℝ)
    (i last : Fin n) (hr : r i ≠ 0) (hc : c i ≠ 0) (hM : M ≠ 0)
    (hp : S i i ≠ 0) :
    signedScale S r c M last i / signedScale S r c M i i =
      (r last / r i) * (S last i / S i i) := by
  unfold signedScale
  field_simp

/-- Normalize the initial maximum, pivot signs, and lower multipliers in a chosen row.
The statement preserves every entry magnitude at every stage, including the padded zeros. -/
theorem exists_normalized_noSwap {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hp : AdmissiblePath A (noSwapPath n)) (last : Fin n) :
    ∃ B : Mat n,
      AdmissiblePath B (noSwapPath n) ∧
      (∀ i j, |B i j| ≤ 1) ∧
      (∀ i : Fin n, 0 < trajectory B (noSwapPath n) i.val i i) ∧
      (∀ i : Fin n, i < last →
        0 ≤ trajectory B (noSwapPath n) i.val last i /
          trajectory B (noSwapPath n) i.val i i) ∧
      (∀ k : ℕ, ∀ i j : Fin n,
        |trajectory B (noSwapPath n) k i j| =
          |trajectory A (noSwapPath n) k i j| / entryMax A) := by
  let M := entryMax A
  have hM : 0 < M := entryMax_pos_of_admissible_proved hn A (noSwapPath n) hp
  let S := trajectory A (noSwapPath n)
  let p := fun i : Fin n => S i.val i i
  let L := fun i : Fin n => S i.val last i / p i
  let r := fun i : Fin n => if i = last then (1 : ℝ) else unitSign (L i)
  let c := fun i : Fin n => r i * unitSign (p i)
  let B := signedScale A r c M
  have hr : ∀ i, |r i| = 1 := by
    intro i
    dsimp [r]
    split
    · norm_num
    · exact unitSign_abs _
  have hrs : ∀ i, (r i)^2 = 1 := by
    intro i
    dsimp [r]
    split
    · norm_num
    · exact unitSign_sq _
  have hc : ∀ i, |c i| = 1 := by
    intro i
    simp only [c, abs_mul, hr, unitSign_abs, mul_one]
  have hr0 : ∀ i, r i ≠ 0 := by
    intro i hi
    have := hr i
    simp [hi] at this
  have hc0 : ∀ i, c i ≠ 0 := fun i => mul_ne_zero (hr0 i) (unitSign_ne_zero _)
  have hp0 : ∀ i, p i ≠ 0 := fun i => (hp i).2.2.1
  have htraj : ∀ k, trajectory B (noSwapPath n) k = signedScale (S k) r c M :=
    fun k => trajectory_signedScale A r c M hr0 hc0 hM.ne' hp k
  have habs : ∀ k : ℕ, ∀ i j : Fin n,
      |trajectory B (noSwapPath n) k i j| = |S k i j| / M := by
    intro k i j
    rw [htraj]
    exact signedScale_abs _ r c M hr hc hM i j
  have hpB : ∀ i : Fin n, trajectory B (noSwapPath n) i.val i i = |p i| / M := by
    intro i
    rw [htraj]
    change r i * p i * (r i * unitSign (p i)) / M = |p i| / M
    rw [show r i * p i * (r i * unitSign (p i)) =
      (r i)^2 * (unitSign (p i) * p i) by ring, hrs, unitSign_mul, one_mul]
  refine ⟨B, admissiblePath_signedScale A r c M hr hc hM hp, ?_, ?_, ?_, habs⟩
  · intro i j
    change |signedScale A r c M i j| ≤ 1
    rw [signedScale_abs _ r c M hr hc hM, div_le_one hM]
    exact abs_le_entryMax_proved A i j
  · intro i
    rw [hpB]
    exact div_pos (abs_pos.mpr (hp0 i)) hM
  · intro i hi
    rw [htraj]
    rw [signedScale_multiplier _ r c M i last (hr0 i) (hc0 i) hM.ne' (hp0 i)]
    have hrlast : r last = 1 := by simp [r]
    have hri : r i = unitSign (L i) := by simp [r, ne_of_lt hi]
    rw [hrlast, hri, one_div, unitSign_inv]
    change 0 ≤ unitSign (L i) * L i
    rw [unitSign_mul]
    exact abs_nonneg _

end NLA.IE15

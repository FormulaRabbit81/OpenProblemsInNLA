/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of Technology.
The finite-maximum proofs are adapted from the same author's IE-05 GEPP.lean
at upstream c7f399b1694e0a68756e8d060e2a71775c044301. Rook steps additionally
interchange columns and require both pivot-row and pivot-column maxima.
Implementation uses substantial OpenAI Codex assistance.
-/
import NLA.IE15.Definitions
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

noncomputable section
open scoped NNReal
namespace NLA.IE15

theorem entryMax_nonneg_proved {n : ℕ} (A : Mat n) : 0 ≤ entryMax A :=
  (entryMaxNN A).coe_nonneg

theorem activeMax_nonneg_proved {n : ℕ} (S : Mat n) (k : ℕ) : 0 ≤ activeMax S k :=
  (activeMaxNN S k).coe_nonneg

theorem abs_le_entryMax_proved {n : ℕ} (A : Mat n) (i j : Fin n) :
    |A i j| ≤ entryMax A := by
  have h : ‖A i j‖₊ ≤ entryMaxNN A :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ (i, j))
  have hc := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm, Real.norm_eq_abs, entryMax] using hc

theorem abs_le_activeMax_proved {n : ℕ} (S : Mat n) (k : ℕ) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) : |S i j| ≤ activeMax S k := by
  have h : ‖S i j‖₊ ≤ activeMaxNN S k := by
    simpa only [activeMaxNN, hi, hj, and_self, if_true] using
      (Finset.le_sup (s := Finset.univ)
        (f := fun ij : Fin n × Fin n =>
          if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)
        (Finset.mem_univ (i, j)))
  have hc := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm, Real.norm_eq_abs, activeMax] using hc

theorem activeMax_le_proved {n : ℕ} (S : Mat n) (k : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ i j, k ≤ i.val → k ≤ j.val → |S i j| ≤ C) :
    activeMax S k ≤ C := by
  have hnn : activeMaxNN S k ≤ ⟨C, hC⟩ := by
    apply Finset.sup_le
    intro ij _
    by_cases hij : k ≤ ij.1.val ∧ k ≤ ij.2.val
    · simp only [if_pos hij]
      apply NNReal.coe_le_coe.mp
      change ‖S ij.1 ij.2‖ ≤ C
      simpa only [Real.norm_eq_abs] using h ij.1 ij.2 hij.1 hij.2
    · simp only [if_neg hij]
      exact bot_le
  exact NNReal.coe_le_coe.mpr hnn

theorem entryMax_semantics_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, |A i j| ≤ entryMax A) ∧
      ∃ i j, entryMax A = |A i j| := by
  refine ⟨entryMax_nonneg_proved A, abs_le_entryMax_proved A, ?_⟩
  let z : Fin n := ⟨0, by omega⟩
  obtain ⟨ij, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => ‖A ij.1 ij.2‖₊) ⟨(z, z), Finset.mem_univ _⟩
  have he : entryMaxNN A = ‖A ij.1 ij.2‖₊ :=
    le_antisymm (Finset.sup_le hmax)
      (Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ ij))
  refine ⟨ij.1, ij.2, ?_⟩
  simpa only [entryMax, coe_nnnorm, Real.norm_eq_abs] using congrArg NNReal.toReal he

theorem activeMax_zero_proved {n : ℕ} (S : Mat n) : activeMax S 0 = entryMax S := by
  simp [activeMax, activeMaxNN, entryMax, entryMaxNN]

theorem entryMax_le_proved {n : ℕ} (A : Mat n) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, |A i j| ≤ C) : entryMax A ≤ C := by
  rw [← activeMax_zero_proved]
  exact activeMax_le_proved A 0 C hC (fun i j _ _ => h i j)

theorem swap_active_proved {n : ℕ} (k p i : Fin n) (hp : k ≤ p) (hi : k ≤ i) :
    k ≤ Equiv.swap k p i := by
  by_cases hik : i = k
  · subst i; simpa using hp
  · by_cases hip : i = p
    · subst i; simp
    · simpa [Equiv.swap_apply_of_ne_of_ne hik hip] using hi

/-- Rook pivoting, like partial pivoting, permits at most a factor two per step. -/
theorem schurStep_bound_proved {n : ℕ} (S : Mat n) (k r c : Fin n)
    (hp : AdmissiblePivot S k r c) :
    activeMax (schurStep S k r c) (k.val + 1) ≤ 2 * activeMax S k.val := by
  rcases hp with ⟨hr, hc, hp, hrow, hcol⟩
  let B := pivotSwap S k r c
  let M := activeMax S k.val
  have hM : 0 ≤ M := activeMax_nonneg_proved S k.val
  have hb : ∀ i j, k ≤ i → k ≤ j → |B i j| ≤ M := by
    intro i j hi hj
    exact abs_le_activeMax_proved S k.val (Equiv.swap k r i) (Equiv.swap k c j)
      (swap_active_proved k r i hr hi) (swap_active_proved k c j hc hj)
  have hkk : B k k = S r c := by simp [B, pivotSwap]
  have hpos : 0 < |B k k| := abs_pos.mpr (hkk ▸ hp)
  apply activeMax_le_proved _ _ _ (mul_nonneg (by norm_num) hM)
  intro i j hi hj
  have hki : k < i := hi
  have hkj : k < j := hj
  have hmult : |B i k / B k k| ≤ 1 := by
    rw [abs_div, div_le_one hpos, hkk]
    simpa [B, pivotSwap] using hcol (Equiv.swap k r i)
      (swap_active_proved k r i hr hki.le)
  change |(if k < i ∧ k < j then B i j - (B i k / B k k) * B k j else 0)| ≤ 2 * M
  rw [if_pos ⟨hki, hkj⟩]
  calc
    |B i j - (B i k / B k k) * B k j| ≤ |B i j| + |(B i k / B k k) * B k j| := by
      simpa using abs_sub_le (B i j) 0 ((B i k / B k k) * B k j)
    _ = |B i j| + |B i k / B k k| * |B k j| := by rw [abs_mul]
    _ ≤ M + 1 * M := add_le_add (hb i j hki.le hkj.le)
      (mul_le_mul hmult (hb k j le_rfl hkj.le) (abs_nonneg _) (by norm_num))
    _ = 2 * M := by ring

/-- The actual finite numerator in the frozen definition of `growth`. -/
def peakMax {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ)

theorem activeMax_le_peakMax_proved {n : ℕ} (A : Mat n) (path : PivotPath n) (k : Fin n) :
    activeMax (trajectory A path k.val) k.val ≤ peakMax A path :=
  NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) (Finset.mem_univ k))

theorem peakMax_le_proved {n : ℕ} (A : Mat n) (path : PivotPath n) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ k : Fin n, activeMax (trajectory A path k.val) k.val ≤ C) :
    peakMax A path ≤ C := by
  have hnn : (Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) ≤ ⟨C,hC⟩ := by
    apply Finset.sup_le
    intro k _
    exact NNReal.coe_le_coe.mp (h k)
  exact NNReal.coe_le_coe.mpr hnn

theorem entryMax_le_peakMax_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n) (path : PivotPath n) :
    entryMax A ≤ peakMax A path := by
  have h := activeMax_le_peakMax_proved A path (⟨0, by omega⟩ : Fin n)
  simpa only [trajectory, activeMax_zero_proved] using h

theorem rook_stage_bound_proved {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hp : AdmissiblePath A path) (k : ℕ) (hk : k < n) :
    activeMax (trajectory A path k) k ≤ (2 : ℝ)^k * entryMax A := by
  induction k with
  | zero => simp [trajectory, activeMax_zero_proved]
  | succ k ih =>
    have hkn : k < n := by omega
    have hs := schurStep_bound_proved (trajectory A path k) ⟨k,hkn⟩
      (path ⟨k,hkn⟩).1 (path ⟨k,hkn⟩).2 (hp ⟨k,hkn⟩)
    calc
      activeMax (trajectory A path (k+1)) (k+1) ≤ 2 * activeMax (trajectory A path k) k := by
        simpa only [trajectory, dif_pos hkn] using hs
      _ ≤ 2 * ((2:ℝ)^k * entryMax A) :=
        mul_le_mul_of_nonneg_left (ih hkn) (by norm_num)
      _ = (2:ℝ)^(k+1) * entryMax A := by ring

theorem entryMax_pos_of_admissible_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (path : PivotPath n) (hp : AdmissiblePath A path) : 0 < entryMax A := by
  let z : Fin n := ⟨0, by omega⟩
  have hz : A (path z).1 (path z).2 ≠ 0 := by
    simpa [z, trajectory] using (hp z).2.2.1
  exact lt_of_lt_of_le (abs_pos.mpr hz)
    (abs_le_entryMax_proved A (path z).1 (path z).2)

theorem growth_le_of_entries_proved {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (path : PivotPath n) (hp : AdmissiblePath A path) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k i j : Fin n, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ C * entryMax A) : growth A path ≤ C := by
  have hE := entryMax_pos_of_admissible_proved hn A path hp
  change peakMax A path / entryMax A ≤ C
  apply (div_le_iff₀ hE).mpr
  apply peakMax_le_proved _ _ _ (mul_nonneg hC hE.le)
  intro k
  apply activeMax_le_proved _ _ _ (mul_nonneg hC hE.le)
  exact fun i j hi hj => h k i j hi hj


end NLA.IE15

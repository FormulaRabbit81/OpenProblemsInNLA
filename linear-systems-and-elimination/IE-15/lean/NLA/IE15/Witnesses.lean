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

/-- Exact evaluation of the first order-three Schur step, including zero padding. -/
theorem witness3_stage_one_proved :
    trajectory witness3 (noSwapPath 3) 1 =
      !![0, 0, 0; 0, 1, -1; 0, 1, 2] := by
  rw [trajectory, dif_pos (by decide : 0 < 3), trajectory]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [schurStep, pivotSwap, noSwapPath, witness3]

/-- Exact evaluation of the second order-three Schur step. -/
theorem witness3_stage_two_proved :
    trajectory witness3 (noSwapPath 3) 2 =
      !![0, 0, 0; 0, 0, 0; 0, 0, 3] := by
  rw [trajectory, dif_pos (by decide : 1 < 3), witness3_stage_one_proved]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [schurStep, pivotSwap, noSwapPath, Matrix.cons_val_succ', Matrix.cons_val_two, Fin.lt_def]

/-- Exact evaluation of the first order-four Schur step. -/
theorem witness4_stage_one_proved :
    trajectory witness4 (noSwapPath 4) 1 =
      !![0, 0, 0, 0; 0, 1, 1/3, -1; 0, -1, 4/3, -2/3; 0, 1, 2, 2] := by
  rw [trajectory, dif_pos (by decide : 0 < 4), trajectory]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [schurStep, pivotSwap, noSwapPath, witness4]

/-- Exact evaluation of the second order-four Schur step. -/
theorem witness4_stage_two_proved :
    trajectory witness4 (noSwapPath 4) 2 =
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 5/3, -5/3; 0, 0, 5/3, 3] := by
  rw [trajectory, dif_pos (by decide : 1 < 4), witness4_stage_one_proved]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [schurStep, pivotSwap, noSwapPath, Matrix.cons_val_succ', Matrix.cons_val_two, Fin.lt_def]

/-- Exact evaluation of the last order-four Schur step. -/
theorem witness4_stage_three_proved :
    trajectory witness4 (noSwapPath 4) 3 =
      !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 14/3] := by
  rw [trajectory, dif_pos (by decide : 2 < 4), witness4_stage_two_proved]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [schurStep, pivotSwap, noSwapPath, Matrix.cons_val_succ', Matrix.cons_val_two, Fin.lt_def]

theorem witness3_det_proved : witness3.det = 3 := by
  norm_num [witness3, Matrix.det_fin_three, Matrix.cons_val_succ', Matrix.cons_val_two]

theorem witness4_det_proved : witness4.det = (70/9 : ℝ) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three]
  norm_num [Matrix.submatrix, witness4, Matrix.cons_val_two, Fin.succAbove,
    Fin.lt_def, Fin.le_def, Fin.castSucc, Fin.castAdd, Fin.castLE]

theorem witness3_admissible_proved : AdmissiblePath witness3 (noSwapPath 3) := by
  intro k
  fin_cases k <;>
    dsimp only [Fin.val] <;>
    (try simp only [witness3_stage_one_proved, witness3_stage_two_proved]) <;>
    norm_num [AdmissiblePivot, noSwapPath, trajectory, witness3, Matrix.cons_val_succ', Matrix.cons_val_two,
      schurStep, pivotSwap, Fin.lt_def, Fin.le_def] <;>
    constructor <;> intro j <;> fin_cases j <;>
    norm_num [Matrix.cons_val_succ', Matrix.cons_val_two, Fin.le_def, Fin.lt_def]

theorem witness4_admissible_proved : AdmissiblePath witness4 (noSwapPath 4) := by
  intro k
  fin_cases k <;>
    dsimp only [Fin.val] <;>
    (try simp only [witness4_stage_one_proved, witness4_stage_two_proved,
      witness4_stage_three_proved]) <;>
    norm_num [AdmissiblePivot, noSwapPath, trajectory, witness4, Matrix.cons_val_succ', Matrix.cons_val_two,
      schurStep, pivotSwap, Fin.lt_def, Fin.le_def] <;>
    constructor <;> intro j <;> fin_cases j <;>
    norm_num [Matrix.cons_val_succ', Matrix.cons_val_two, Fin.le_def, Fin.lt_def]

/-- The maximum is computed from every actual active entry at every stage. -/
theorem witness3_stage_maxima_proved (k : Fin 3) :
    activeMax (trajectory witness3 (noSwapPath 3) k.val) k.val = ![1, 2, 3] k := by
  apply le_antisymm
  · apply activeMax_le_proved
    · fin_cases k <;> norm_num
    · intro i j _ _
      fin_cases k <;> dsimp only [Fin.val] <;>
        (try simp only [witness3_stage_one_proved, witness3_stage_two_proved]) <;>
        fin_cases i <;> fin_cases j <;> norm_num [trajectory, witness3]
  · have h := abs_le_activeMax_proved (trajectory witness3 (noSwapPath 3) k.val)
      k.val (2 : Fin 3) (2 : Fin 3) (by omega) (by omega)
    fin_cases k <;> dsimp only [Fin.val] at h ⊢
    · change |(1 : ℝ)| ≤ activeMax witness3 0 at h
      change (1 : ℝ) ≤ _
      simpa only [abs_one, trajectory] using h
    · simp only [witness3_stage_one_proved] at h ⊢
      change |(2 : ℝ)| ≤ activeMax _ 1 at h
      rw [abs_of_pos (by norm_num)] at h
      exact h
    · simp only [witness3_stage_two_proved] at h ⊢
      change |(3 : ℝ)| ≤ activeMax _ 2 at h
      rw [abs_of_pos (by norm_num)] at h
      exact h

/-- In particular the second Schur complement has maximum three, not four. -/
theorem witness4_stage_maxima_proved (k : Fin 4) :
    activeMax (trajectory witness4 (noSwapPath 4) k.val) k.val = ![1, 2, 3, 14/3] k := by
  apply le_antisymm
  · apply activeMax_le_proved
    · fin_cases k <;> norm_num
    · intro i j _ _
      fin_cases k <;> dsimp only [Fin.val] <;>
        (try simp only [witness4_stage_one_proved, witness4_stage_two_proved,
          witness4_stage_three_proved]) <;>
        fin_cases i <;> fin_cases j <;> norm_num [trajectory, witness4]
  · have h := abs_le_activeMax_proved (trajectory witness4 (noSwapPath 4) k.val)
      k.val (3 : Fin 4) (3 : Fin 4) (by omega) (by omega)
    fin_cases k <;> dsimp only [Fin.val] at h ⊢
    · change |(1 : ℝ)| ≤ activeMax witness4 0 at h
      change (1 : ℝ) ≤ _
      simpa only [abs_one, trajectory] using h
    · simp only [witness4_stage_one_proved] at h ⊢
      change |(2 : ℝ)| ≤ activeMax _ 1 at h
      rw [abs_of_pos (by norm_num)] at h
      exact h
    · simp only [witness4_stage_two_proved] at h ⊢
      change |(3 : ℝ)| ≤ activeMax _ 2 at h
      rw [abs_of_pos (by norm_num)] at h
      exact h
    · simp only [witness4_stage_three_proved] at h ⊢
      change |(14/3 : ℝ)| ≤ activeMax _ 3 at h
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 14/3)] at h
      exact h

theorem witness3_entryMax_proved : entryMax witness3 = 1 := by
  simpa only [trajectory, Fin.val_zero, activeMax_zero_proved, Matrix.cons_val_zero] using
    witness3_stage_maxima_proved 0

theorem witness4_entryMax_proved : entryMax witness4 = 1 := by
  simpa only [trajectory, Fin.val_zero, activeMax_zero_proved, Matrix.cons_val_zero] using
    witness4_stage_maxima_proved 0

theorem witness3_growth_proved : growth witness3 (noSwapPath 3) = 3 := by
  have hp : peakMax witness3 (noSwapPath 3) = 3 := by
    apply le_antisymm
    · apply peakMax_le_proved _ _ _ (by norm_num)
      intro k
      rw [witness3_stage_maxima_proved]
      fin_cases k <;> norm_num
    · have h := activeMax_le_peakMax_proved witness3 (noSwapPath 3) (2 : Fin 3)
      rw [witness3_stage_maxima_proved] at h
      simpa [Matrix.cons_val_two] using h
  change peakMax witness3 (noSwapPath 3) / entryMax witness3 = 3
  rw [hp, witness3_entryMax_proved, div_one]

theorem witness4_growth_proved : growth witness4 (noSwapPath 4) = (14/3 : ℝ) := by
  have hp : peakMax witness4 (noSwapPath 4) = (14/3 : ℝ) := by
    apply le_antisymm
    · apply peakMax_le_proved _ _ _ (by norm_num)
      intro k
      rw [witness4_stage_maxima_proved]
      fin_cases k <;> norm_num
    · have h := activeMax_le_peakMax_proved witness4 (noSwapPath 4) (3 : Fin 4)
      rw [witness4_stage_maxima_proved] at h
      exact h
  change peakMax witness4 (noSwapPath 4) / entryMax witness4 = (14/3 : ℝ)
  rw [hp, witness4_entryMax_proved, div_one]

/-- Exact order-three conjunct matching the independently frozen Challenge. -/
theorem witness_three_proved :
    witness3.det = 3 ∧ entryMax witness3 = 1 ∧
      AdmissiblePath witness3 (noSwapPath 3) ∧
      growth witness3 (noSwapPath 3) = 3 :=
  ⟨witness3_det_proved, witness3_entryMax_proved,
    witness3_admissible_proved, witness3_growth_proved⟩

/-- Exact order-four conjunct matching the independently frozen Challenge. -/
theorem witness_four_proved :
    witness4.det = (70/9 : ℝ) ∧ entryMax witness4 = 1 ∧
      AdmissiblePath witness4 (noSwapPath 4) ∧
      growth witness4 (noSwapPath 4) = (14/3 : ℝ) :=
  ⟨witness4_det_proved, witness4_entryMax_proved,
    witness4_admissible_proved, witness4_growth_proved⟩

end NLA.IE15

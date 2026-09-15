/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.Definitions
import Mathlib.Tactic

noncomputable section
open Matrix
namespace NLA.IE17

theorem euclidean_norm_sq_three (y : Vec 3) :
    ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  ring

theorem euclidean_norm_sq_four (y : Vec 4) :
    ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  ring

theorem euclidean_apply_coord {m n : ℕ} (A : Mat m n) (y : Vec n) (i : Fin m) :
    (A.toEuclideanLin y) i = ∑ j, A i j * y j := rfl

theorem witnessX₁_norm_sq : ‖witnessX₁‖ ^ 2 = (189724262 : ℝ) / 973502401 := by
  norm_num [Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, euclidean_norm_sq_three, witnessX₁]

theorem witnessX₂_norm_sq : ‖witnessX₂‖ ^ 2 = (8026273307 : ℝ) / 3049137961 := by
  norm_num [Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, euclidean_norm_sq_three, witnessX₂]

theorem witnessX₃_norm_sq : ‖witnessX₃‖ ^ 2 = (108961 : ℝ) / 900 := by
  norm_num [Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three, euclidean_norm_sq_three, witnessX₃]

theorem witness_residual_one :
    residual witnessA witnessB witnessX₁ =
      WithLp.toLp 2 ![(331980 : ℝ) / 31201, -5555 / 31201, 5676 / 31201, 1] := by
  ext i
  fin_cases i <;>
    norm_num [residual, euclidean_apply_coord, witnessA, witnessB, witnessX₁,
      Fin.sum_univ_succ]

theorem witness_residual_two :
    residual witnessA witnessB witnessX₂ =
      WithLp.toLp 2 ![(519750 : ℝ) / 55219, 9625 / 55219, -29106 / 55219, 1] := by
  ext i
  fin_cases i <;>
    norm_num [residual, euclidean_apply_coord, witnessA, witnessB, witnessX₂,
      Fin.sum_univ_succ]

theorem witness_residual_three :
    residual witnessA witnessB witnessX₃ = WithLp.toLp 2 ![(0 : ℝ), 0, 0, 1] := by
  ext i
  fin_cases i <;>
    norm_num [residual, euclidean_apply_coord, witnessA, witnessB, witnessX₃,
      Fin.sum_univ_succ]

theorem witness_residual_one_norm_sq :
    ‖residual witnessA witnessB witnessX₁‖ ^ 2 =
      (111247297802 : ℝ) / 973502401 := by
  rw [witness_residual_one]
  norm_num [euclidean_norm_sq_four, Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three]

theorem witness_residual_two_norm_sq :
    ‖residual witnessA witnessB witnessX₂‖ ^ 2 =
      (274129000322 : ℝ) / 3049137961 := by
  rw [witness_residual_two]
  norm_num [euclidean_norm_sq_four, Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three]

end NLA.IE17

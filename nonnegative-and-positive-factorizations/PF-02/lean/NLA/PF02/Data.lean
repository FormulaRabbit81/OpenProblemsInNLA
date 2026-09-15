/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.PF02.Definitions
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.NormDet
import Mathlib.Tactic
import LeanCert.Tactic

noncomputable section
open Matrix
namespace NLA.PF02

/-- Exact positive orientation constant, proved by LeanCert in kernel mode. -/
theorem thirty_two_pos : (0 : ℝ) < 32 := by
  interval_decide (trust := kernel)

/-- Every explicit factor is positive definite, for either of the two signs. -/
theorem witnessFactors_posDef (s : ℝ) (hs : s = 1 ∨ s = -1) (i : Fin 6) :
    (witnessFactors s i).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [witnessFactors]
  · intro x hx
    have hpos : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
      have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
        by_contra h
        push Not at h
        apply hx
        ext j
        fin_cases j <;> simp_all
      rcases hne with h | h | h <;>
        nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0),
          sq_nonneg (x 1), sq_nonneg (x 2)]
    rcases hs with rfl | rfl <;> fin_cases i <;>
      simp [witnessFactors, dotProduct, mulVec, Fin.sum_univ_succ] <;>
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
        sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
        sq_nonneg (x 0 + x 2), sq_nonneg (x 1 + x 2)]

/-- All thirty-six trace equations, at either sign. -/
theorem witness_trace (s : ℝ) (hs : s = 1 ∨ s = -1) (i j : Fin 6) :
    Matrix.trace (witnessFactors s i * witnessFactors s j) = witnessM i j := by
  rcases hs with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    norm_num [witnessFactors, witnessM, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem explicit_factorizations :
    IsFactorization witnessM (witnessTuple 1) ∧
    IsFactorization witnessM (witnessTuple (-1)) ∧
    (∀ i, (witnessFactors 1 i).PosDef) ∧
    (∀ i, (witnessFactors (-1) i).PosDef) := by
  have h (s : ℝ) (hs : s = 1 ∨ s = -1) :
      IsFactorization witnessM (witnessTuple s) := by
    exact ⟨fun i => (witnessFactors_posDef s hs i).posSemidef,
      fun i => (witnessFactors_posDef s hs i).posSemidef, witness_trace s hs⟩
  exact ⟨h 1 (Or.inl rfl), h (-1) (Or.inr rfl),
    witnessFactors_posDef 1 (Or.inl rfl), witnessFactors_posDef (-1) (Or.inr rfl)⟩

/-- Literal coordinates, with a free real sign parameter. -/
theorem rowCoordinates_witness (s : ℝ) : rowCoordinates (witnessFactors s) =
    !![4,2,2,0,0,0; 2,4,2,0,0,0; 2,2,4,0,0,0;
       2,2,2,s,0,0; 2,2,2,0,1,0; 2,2,2,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowCoordinates, coord, witnessFactors]

theorem witness_coordinate_det (s : ℝ) :
    (rowCoordinates (witnessFactors s)).det = 32 * s := by
  rw [rowCoordinates_witness]
  eval_det
  ring

theorem witness_matrix_det : witnessM.det = 8192 := by
  unfold witnessM
  eval_det

theorem witness_numeric_data :
    (∀ i j, 0 < witnessM i j) ∧ witnessM.det = 8192 ∧ witnessM.rank = 6 ∧
    (rowCoordinates (witnessFactors 1)).det = 32 ∧
    (rowCoordinates (witnessFactors (-1))).det = -32 := by
  refine ⟨?_, witness_matrix_det, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessM]
  · simpa using Matrix.rank_of_det_ne_zero (A := witnessM) (by rw [witness_matrix_det]; norm_num)
  · simpa using witness_coordinate_det 1
  · simpa using witness_coordinate_det (-1)

#assert_trust kernel thirty_two_pos
#assert_trust kernel explicit_factorizations
#assert_trust kernel witness_numeric_data
#print axioms thirty_two_pos
#print axioms explicit_factorizations
#print axioms witness_numeric_data

end NLA.PF02

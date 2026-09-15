/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Definitions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

lemma gram_charpoly_eval (U : Mat 3) (z : ℝ) :
    (Uᵀ * U).charpoly.eval z = gramPolynomialValue U z := by
  rw [Matrix.eval_charpoly]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar, h]

lemma continuous_gram_value (z : ℝ) : Continuous (fun U : Mat 3 => gramPolynomialValue U z) := by
  unfold gramPolynomialValue
  fun_prop

lemma family_isOpen : IsOpen counterexampleFamily := by
  unfold counterexampleFamily
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt
    ((continuous_gram_value ((lowerEndpoint i)^2)).mul
      (continuous_gram_value ((upperEndpoint i)^2))) continuous_const

lemma gram_diagonal_value (s : Fin 3 → ℝ) (z : ℝ) :
    gramPolynomialValue (Matrix.diagonal s) z = ∏ i, (z - (s i)^2) := by
  unfold gramPolynomialValue
  have hm : z • (1 : Mat 3) - (Matrix.diagonal s)ᵀ * Matrix.diagonal s =
      Matrix.diagonal (fun i => z - (s i)^2) := by
    ext i j
    by_cases h : i = j <;> simp [h, pow_two]
  rw [hm, Matrix.det_diagonal]

lemma sample_in_family : sampleMatrix ∈ counterexampleFamily := by
  intro i
  change gramPolynomialValue (Matrix.diagonal sampleSingularValues) ((lowerEndpoint i)^2) *
    gramPolynomialValue (Matrix.diagonal sampleSingularValues) ((upperEndpoint i)^2) < 0
  rw [gram_diagonal_value, gram_diagonal_value]
  fin_cases i <;>
    norm_num [sampleSingularValues, lowerEndpoint, upperEndpoint, Fin.prod_univ_three,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

lemma endpoint_sq_lt (i : Fin 3) : (lowerEndpoint i)^2 < (upperEndpoint i)^2 := by
  fin_cases i <;> norm_num [lowerEndpoint, upperEndpoint]

/-- Actual roots of the real Gram characteristic polynomial in three disjoint positive intervals. -/
lemma gram_root_in_interval (U : Mat 3) (hU : U ∈ counterexampleFamily) (i : Fin 3) :
    ∃ r : ℝ, (lowerEndpoint i)^2 < r ∧ r < (upperEndpoint i)^2 ∧
      (Uᵀ * U).charpoly.eval r = 0 := by
  have hc : Continuous (gramPolynomialValue U) := by
    unfold gramPolynomialValue
    fun_prop
  have hprod := hU i
  rcases mul_neg_iff.mp hprod with hsign | hsign
  · obtain ⟨r, hr, hz⟩ := intermediate_value_Ioo' (le_of_lt (endpoint_sq_lt i))
      hc.continuousOn ⟨hsign.2, hsign.1⟩
    exact ⟨r, hr.1, hr.2, (gram_charpoly_eval U r).trans hz⟩
  · obtain ⟨r, hr, hz⟩ := intermediate_value_Ioo (le_of_lt (endpoint_sq_lt i))
      hc.continuousOn hsign
    exact ⟨r, hr.1, hr.2, (gram_charpoly_eval U r).trans hz⟩

end NLA.SP04

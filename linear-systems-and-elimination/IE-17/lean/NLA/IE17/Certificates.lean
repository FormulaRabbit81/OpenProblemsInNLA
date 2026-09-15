/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
The auxiliary congruence and weighted diagonal-dominance certificates were
independently reviewed before implementation; see NUMERICAL_TARGETS.md §§4.1,5.1.
-/
import NLA.IE17.NumericData
import LeanCert.Tactic

noncomputable section
open Matrix
namespace NLA.IE17

/-- Exact cutoffs consumed by the optimal-error comparison, certified in kernel mode. -/
theorem certificate_cutoffs :
    0 < (1979 : ℝ) / 2000 ∧
    (1979 : ℝ) / 2000 < (99 : ℝ) / 100 ∧
    (99 : ℝ) / 100 < (9901 : ℝ) / 10000 := by
  refine ⟨?_, ?_, ?_⟩ <;> interval_decide (trust := kernel)

/-- The full rational feasible perturbation from the original completion. -/
def witnessE : Mat 4 3 := fun i j =>
  (!![(-165210014935131560 : ℝ), 11610848662197240, 2530244735132700;
      39351326577989, -69867125644099962, -53313444486018375;
      -21561235850426, 71865739948107360, 54839250040764540;
      -18526767941430855, -75599190148266018, -58398875034268035] i j) /
        167211149523055806

theorem witnessE_feasible : Feasible witnessA witnessB witnessX₁ witnessE := by
  unfold Feasible normalResidual
  ext i
  change (∑ j : Fin 4, (witnessA j i + witnessE j i) *
    (witnessB j - ∑ k : Fin 3, (witnessA j k + witnessE j k) * witnessX₁ k)) = 0
  fin_cases i <;>
    norm_num [witnessA, witnessB, witnessX₁, witnessE, Fin.sum_univ_succ, Fin.succ,
      Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three]

/-- Signed-square expansion of the reviewed three-dimensional dominance certificate. -/
private def upperSOS (a b c : ℝ) : ℝ :=
  11610303162792839972527905686 * a ^ 2 +
  2422484425274344247124223382031 * b ^ 2 +
  3388031261437186722083054351461 * c ^ 2 +
  12090505500201922856789273706 * (a + b) ^ 2 +
  8382094473667110912199943291 * (a - c) ^ 2 +
  31049384466533821447752395238 * (b + c) ^ 2

private theorem upperSOS_nonneg (a b c : ℝ) : 0 ≤ upperSOS a b c := by
  unfold upperSOS
  positivity

/-- T⁻¹y has coordinates (y₀+18y₁−23y₂,y₁,y₂); this is exactly TᵀGT=M/dM. -/
private theorem upper_sos_identity (y : Vec 3) :
    31584381671763314443807585554000 *
      ((1979 : ℝ) / 2000 * ‖y‖ ^ 2 - ‖witnessE.toEuclideanLin y‖ ^ 2) =
    upperSOS (y 0 + 18 * y 1 - 23 * y 2) (y 1) (y 2) := by
  norm_num [upperSOS, euclidean_norm_sq_three, euclidean_norm_sq_four,
    euclidean_apply_coord, witnessE, Fin.sum_univ_succ, Fin.succ,
    Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three]
  simp only [show (Fin.succ 0 : Fin 3) = 1 from rfl,
    show ((Fin.succ 0).succ : Fin 3) = 2 from rfl]
  ring

/-- An every-real-vector Euclidean norm bound, not an entrywise matrix-norm bound. -/
theorem witnessE_norm_sq_bound (y : Vec 3) :
    ‖witnessE.toEuclideanLin y‖ ^ 2 ≤ (1979 : ℝ) / 2000 * ‖y‖ ^ 2 := by
  have h : 0 ≤ 31584381671763314443807585554000 *
      ((1979 : ℝ) / 2000 * ‖y‖ ^ 2 - ‖witnessE.toEuclideanLin y‖ ^ 2) := by
    rw [upper_sos_identity]
    exact upperSOS_nonneg _ _ _
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h (by norm_num))

/-- Signed-square expansion for diag(v)K*diag(v), v=(10000,10,185,1287).
The diagonal coefficients are vᵢ times the reviewed weighted margins.
The off-diagonal coefficients are |Kᵢⱼ|vᵢvⱼ. -/
private def lowerSOS (a b c d : ℝ) : ℝ :=
  (6102817984650 * 10000) * a ^ 2 +
  ((2612912207614679 : ℝ) / 10 * 10) * b ^ 2 +
  ((1352621546092623 : ℝ) / 20 * 185) * c ^ 2 +
  ((1055456050659373 : ℝ) / 100 * 1287) * d ^ 2 +
  (50293465200 * 10000 * 10) * (a - b) ^ 2 +
  (1125984433750 * 10000 * 185) * (a + c) ^ 2 +
  (1435003762500 * 10000 * 1287) * (a - d) ^ 2 +
  (206242965000 * 10 * 185) * (b + c) ^ 2 +
  (26574143750 * 10 * 1287) * (b - d) ^ 2 +
  (80360210700 * 185 * 1287) * (c + d) ^ 2

private theorem lowerSOS_nonneg (a b c d : ℝ) : 0 ≤ lowerSOS a b c d := by
  unfold lowerSOS
  positivity

/-- The original (5/6)C+(1/6)D₂ quadratic form in Euclidean coordinates. -/
def lowerQuadratic (u : Vec 4) : ℝ :=
  (5 : ℝ) / 6 * ‖witnessA.transpose.toEuclideanLin u‖ ^ 2 +
  (1 : ℝ) / 6 *
    (‖residual witnessA witnessB witnessX₂‖ ^ 2 * ‖u‖ ^ 2 -
      (∑ i, residual witnessA witnessB witnessX₂ i * u i) ^ 2 +
      (∑ i, (witnessA.toEuclideanLin witnessX₂) i * u i) ^ 2) /
      ‖witnessX₂‖ ^ 2

private theorem lower_sos_identity (u : Vec 4) :
    2407881992100 * (lowerQuadratic u - (9901 : ℝ) / 10000 * ‖u‖ ^ 2) =
    lowerSOS (u 0 / 10000) (u 1 / 10) (u 2 / 185) (u 3 / 1287) := by
  unfold lowerQuadratic
  rw [witness_residual_two_norm_sq, witnessX₂_norm_sq, witness_residual_two]
  norm_num [lowerSOS, euclidean_norm_sq_three, euclidean_norm_sq_four,
    euclidean_apply_coord, witnessA, witnessX₂, Fin.sum_univ_succ, Fin.succ,
    Matrix.transpose_apply, Matrix.cons_val_succ', Matrix.cons_val_two,
    Matrix.cons_val_three]
  simp only [show (Fin.succ 0 : Fin 4) = 1 from rfl,
    show ((Fin.succ 0).succ : Fin 4) = 2 from rfl,
    show ((Fin.succ 0).succ.succ : Fin 4) = 3 from rfl]
  ring

/-- Uniform lower bound for every real direction; the original cutoff is 99/100. -/
theorem lower_quadratic_certificate (u : Vec 4) :
    (9901 : ℝ) / 10000 * ‖u‖ ^ 2 ≤
      (5 : ℝ) / 6 * ‖witnessA.transpose.toEuclideanLin u‖ ^ 2 +
      (1 : ℝ) / 6 *
        (‖residual witnessA witnessB witnessX₂‖ ^ 2 * ‖u‖ ^ 2 -
          (∑ i, residual witnessA witnessB witnessX₂ i * u i) ^ 2 +
          (∑ i, (witnessA.toEuclideanLin witnessX₂) i * u i) ^ 2) /
          ‖witnessX₂‖ ^ 2 := by
  change (9901 : ℝ) / 10000 * ‖u‖ ^ 2 ≤ lowerQuadratic u
  have h : 0 ≤ 2407881992100 *
      (lowerQuadratic u - (9901 : ℝ) / 10000 * ‖u‖ ^ 2) := by
    rw [lower_sos_identity]
    exact lowerSOS_nonneg _ _ _ _
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h (by norm_num))

/-- The zero-new-residual perturbation case also has the same uniform margin. -/
theorem zero_new_residual_certificate :
    (9901 : ℝ) / 10000 * ‖witnessX₂‖ ^ 2 ≤
      ‖residual witnessA witnessB witnessX₂‖ ^ 2 := by
  rw [witnessX₂_norm_sq, witness_residual_two_norm_sq]
  norm_num

#assert_trust kernel certificate_cutoffs
#assert_trust kernel witnessE_feasible
#assert_trust kernel witnessE_norm_sq_bound
#assert_trust kernel lower_quadratic_certificate
#assert_trust kernel zero_new_residual_certificate

end NLA.IE17

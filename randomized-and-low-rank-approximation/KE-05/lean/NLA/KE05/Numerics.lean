import NLA.KE05.Definitions

/- Exact rational data from George Stepaniants's KE-05 proof.
The spectral norm is reduced to a rank-one operator on Euclidean space. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.KE05

lemma rational_omega_one : omega rationalSample 1 = (1 : Mat 2) := rfl
lemma rational_omega_two : omega rationalSample 2 = (!![1, 2; 3, 5] : Mat 2) := rfl

lemma rational_X : X rationalSample = !![1, 0; 0, 2] := by
  rw [X, rational_omega_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

lemma rational_P : P rationalSample = !![6, 10; -3, -5] := by
  rw [P, rational_omega_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
      Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

lemma rational_kappa : kappa rationalSample = 7 := by
  norm_num [kappa, rational_P, rational_X, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.one_apply]

lemma rational_Q : Q rationalSample = !![30, 50; -18, -30] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, rational_P, rational_X, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.one_apply]

lemma rational_limit : limitMatrix rationalSample = (1 / 7 : ℝ) • !![-30, -50; 18, 30] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [limitMatrix, rational_Q, rational_kappa]

lemma rational_limit_norm : spectralNorm (limitMatrix rationalSample) = (68 : ℝ) / 7 := by
  let u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-5, 3]
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![6 / 7, 10 / 7]
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (limitMatrix rationalSample) =
      InnerProductSpace.rankOne ℝ u v := by
    ext x i
    fin_cases i <;>
      simp [rational_limit, Matrix.ofLp_toEuclideanCLM, InnerProductSpace.rankOne_def,
        u, v, PiLp.inner_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;> ring
  rw [spectralNorm, he, InnerProductSpace.norm_rankOne]
  have hu : ‖u‖ ^ 2 = 34 := by norm_num [EuclideanSpace.real_norm_sq_eq, u, Fin.sum_univ_two]
  have hv : ‖v‖ ^ 2 = 136 / 49 := by norm_num [EuclideanSpace.real_norm_sq_eq, v, Fin.sum_univ_two]
  have hp : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hh : (‖u‖ * ‖v‖) ^ 2 = (68 / 7 : ℝ) ^ 2 := by
    rw [mul_pow, hu, hv]
    norm_num
  nlinarith

 theorem exact_rational_witness_proved :
    X rationalSample = !![1, 0; 0, 2] ∧
    P rationalSample = !![6, 10; -3, -5] ∧
    kappa rationalSample = 7 ∧ Q rationalSample = !![30, 50; -18, -30] ∧
    spectralNorm (limitMatrix rationalSample) = (68 : ℝ) / 7 :=
  ⟨rational_X, rational_P, rational_kappa, rational_Q, rational_limit_norm⟩

end NLA.KE05

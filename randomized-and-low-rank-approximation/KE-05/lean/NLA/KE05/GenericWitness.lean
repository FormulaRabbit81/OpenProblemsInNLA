import NLA.KE05.RegularMatrix
import NLA.KE05.Numerics

/- The rational sample is used exclusively as a nonzero-polynomial witness.
Its probability is never assumed positive. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.KE05

lemma regular_omega {b d : ℕ} (a : Sample b d) (i : Fin d) (r c : Fin b) :
    RegularAt a (fun w => omega w i r c) := RegularAt.coord (i,r,c)

lemma regular_similarity {σ : Type*} {a : σ → ℝ} {b : ℕ}
    (A : (σ → ℝ) → Mat b) (hA : ∀ i j, RegularAt a (fun x => A x i j))
    (ha : (A a).det ≠ 0) (L : Fin b → ℝ) (i j : Fin b) :
    RegularAt a (fun x => ((A x)⁻¹ * Matrix.diagonal L * A x) i j) := by
  apply regular_matrix_mul
  · apply regular_matrix_mul
    · exact regular_matrix_inv A hA ha
    · intro r c
      exact RegularAt.const _
  · exact hA

lemma regular_X (a : Sample 2 3) (ha : (omega a 1).det ≠ 0) (i j : Fin 2) :
    RegularAt a (fun w => X w i j) :=
  regular_similarity (fun w => omega w 1) (regular_omega a 1) ha ![1,2] i j

lemma regular_P (a : Sample 2 3) (ha : (omega a 2).det ≠ 0) (i j : Fin 2) :
    RegularAt a (fun w => P w i j) :=
  regular_similarity (fun w => omega w 2) (regular_omega a 2) ha ![0,1] i j

lemma regular_kappa (a : Sample 2 3) (h1 : (omega a 1).det ≠ 0)
    (h2 : (omega a 2).det ≠ 0) : RegularAt a kappa := by
  apply regular_matrix_trace
  apply regular_matrix_mul
  · intro i j
    exact (RegularAt.const _).sub (regular_P a h2 i j)
  · exact regular_X a h1

lemma regular_Q (a : Sample 2 3) (h1 : (omega a 1).det ≠ 0)
    (h2 : (omega a 2).det ≠ 0) (i j : Fin 2) : RegularAt a (fun w => Q w i j) := by
  apply regular_matrix_mul
  · apply regular_matrix_mul
    · intro r c
      exact (RegularAt.const _).sub (regular_P a h2 r c)
    · exact regular_X a h1
  · exact regular_P a h2

lemma nonzero_limit_numerators_ae : ∀ᵐ w ∂gaussianLaw 2 3,
    kappa w ≠ 0 ∧ Q w 0 0 ≠ 0 := by
  have h1 : (omega rationalSample 1).det ≠ 0 := by rw [rational_omega_one]; norm_num
  have h2 : (omega rationalSample 2).det ≠ 0 := by rw [rational_omega_two]; norm_num [Matrix.det_fin_two]
  have hk := (regular_kappa rationalSample h1 h2).ae_ne_zero (by rw [rational_kappa]; norm_num)
  have hq := (regular_Q rationalSample h1 h2 0 0).ae_ne_zero (by rw [rational_Q]; norm_num)
  exact hk.and hq

end NLA.KE05

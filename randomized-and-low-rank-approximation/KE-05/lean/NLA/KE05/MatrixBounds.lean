import NLA.KE05.Definitions

/- Dimension-two determinant bound for the genuine Euclidean operator norm.
Only two unit coordinate vectors are needed; no singular-value computation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.KE05

lemma spectralNorm_nonneg {b : ℕ} (A : Mat b) : 0 ≤ spectralNorm A := norm_nonneg _

lemma column_squared_le (A : Mat 2) (j : Fin 2) :
    A 0 j ^ 2 + A 1 j ^ 2 ≤ spectralNorm A ^ 2 := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) A
  let u : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single j 1
  have hu : ‖u‖ = 1 := by simp [u]
  have h := T.le_opNorm u
  rw [hu, mul_one] at h
  have hs := (sq_le_sq₀ (norm_nonneg (T u)) (norm_nonneg T)).mpr h
  have he : ‖T u‖ ^ 2 = A 0 j ^ 2 + A 1 j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [T, u, Fin.sum_univ_two, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
      EuclideanSpace.single, Pi.single_apply]
  rw [he] at hs
  exact hs

lemma abs_det_le_spectralNorm_squared (A : Mat 2) : |A.det| ≤ spectralNorm A ^ 2 := by
  have h0 := column_squared_le A 0
  have h1 := column_squared_le A 1
  have hp := mul_le_mul h0 h1 (by positivity : 0 ≤ A 0 1 ^ 2 + A 1 1 ^ 2)
    (by positivity : 0 ≤ spectralNorm A ^ 2)
  have hi : A.det ^ 2 ≤ (spectralNorm A ^ 2) ^ 2 := by
    rw [Matrix.det_fin_two]
    nlinarith [sq_nonneg (A 0 0 * A 0 1 + A 1 0 * A 1 1)]
  have ha : |A.det| ^ 2 = A.det ^ 2 := sq_abs _
  nlinarith [abs_nonneg A.det, sq_nonneg (spectralNorm A)]

lemma inverse_norm_squared_lower (S : Mat 2) (hS : 0 < S.det) (h8 : S.det ≤ 8) :
    (1 : ℝ) / 8 ≤ spectralNorm S⁻¹ ^ 2 := by
  have hd := S.det_nonsing_inv_mul_det hS.ne'.isUnit
  have hb := abs_det_le_spectralNorm_squared S⁻¹
  have hi : 0 ≤ (S⁻¹).det := by nlinarith
  rw [abs_of_nonneg hi] at hb
  have hmul := mul_le_mul_of_nonneg_right hb hS.le
  have hbound := mul_le_mul_of_nonneg_left h8 (sq_nonneg (spectralNorm S⁻¹))
  nlinarith

lemma inverse_half_norm_lower (S : Mat 2) (hS : 0 < S.det) (h8 : S.det ≤ 8) :
    Real.rpow 8 (-(1 : ℝ)/4) ≤ Real.rpow (spectralNorm S⁻¹) ((1 : ℝ)/2) := by
  let x := Real.rpow (spectralNorm S⁻¹) ((1 : ℝ)/2)
  let y := Real.rpow 8 (-(1 : ℝ)/4)
  have hn := spectralNorm_nonneg S⁻¹
  have hx : 0 ≤ x := Real.rpow_nonneg hn _
  have hy : 0 ≤ y := Real.rpow_nonneg (by norm_num) _
  have hx2 : x ^ 2 = spectralNorm S⁻¹ := by
    dsimp only [x]
    have h := Real.rpow_mul_natCast hn ((1 : ℝ)/2) 2
    norm_num at h
    exact h.symm
  have hy4 : y ^ 4 = (1 : ℝ)/8 := by
    dsimp only [y]
    calc
      _ = Real.rpow 8 ((-(1 : ℝ)/4)*4) :=
        (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 8) (-(1 : ℝ)/4) 4).symm
      _ = (1 : ℝ)/8 := by norm_num

  have hb := inverse_norm_squared_lower S hS h8
  have hsq : (y ^ 2) ^ 2 ≤ spectralNorm S⁻¹ ^ 2 := by nlinarith only [hy4, hb]
  have hny : y ^ 2 ≤ spectralNorm S⁻¹ := (sq_le_sq₀ (sq_nonneg y) hn).mp hsq
  change y ≤ x
  exact (sq_le_sq₀ hy hx).mp (by rwa [hx2])

end NLA.KE05

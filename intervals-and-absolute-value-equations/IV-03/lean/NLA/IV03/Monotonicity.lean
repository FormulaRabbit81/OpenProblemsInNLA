/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted exact algebraic Schur monotonicity. The resolvent identity avoids
numerical intervals and differentiation; transfer signs are supplied by the
already proved proper principal inverse-M closure. -/
import NLA.IV03.Cofactor
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma inverse_difference_identity {r : ℕ} (D E : Mat r)
    (hD : IsUnit D) (hE : IsUnit E) : D⁻¹ - E⁻¹ = E⁻¹ * (E-D) * D⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul,
    Matrix.nonsing_inv_mul E ((Matrix.isUnit_iff_isUnit_det _).mp hE), Matrix.one_mul,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det _).mp hD),
    Matrix.mul_one]

lemma matrix_mul_nonnegative {m r n : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ (A * B) i j := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))

lemma schur_bilinear_difference {r : ℕ}
    (l u : Matrix (Fin 1) (Fin r) ℝ) (c v : Matrix (Fin r) (Fin 1) ℝ)
    (D E : Mat r) (hD : IsUnit D) (hE : IsUnit E) :
    u * D⁻¹ * v - l * E⁻¹ * c =
      (u * E⁻¹) * (E-D) * (D⁻¹ * v) +
      (u-l) * (E⁻¹ * v) + (l * E⁻¹) * (v-c) := by
  calc
    _ = u * (D⁻¹ - E⁻¹) * v + (u-l) * E⁻¹ * v + l * E⁻¹ * (v-c) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      abel
    _ = _ := by
      rw [inverse_difference_identity D E hD hE]
      simp only [Matrix.mul_assoc]

lemma schur_bilinear_monotone {r : ℕ}
    (l u : Matrix (Fin 1) (Fin r) ℝ) (c v : Matrix (Fin r) (Fin 1) ℝ)
    (D E : Mat r) (hD : IsUnit D) (hE : IsUnit E)
    (hlu : ∀ i j, l i j ≤ u i j) (hcv : ∀ i j, c i j ≤ v i j)
    (hDE : ∀ i j, D i j ≤ E i j)
    (huE : ∀ i j, 0 ≤ (u * E⁻¹) i j)
    (hDv : ∀ i j, 0 ≤ (D⁻¹ * v) i j)
    (hEv : ∀ i j, 0 ≤ (E⁻¹ * v) i j)
    (hlE : ∀ i j, 0 ≤ (l * E⁻¹) i j) :
    (l * E⁻¹ * c) 0 0 ≤ (u * D⁻¹ * v) 0 0 := by
  have h₁ := matrix_mul_nonnegative (u * E⁻¹) (E-D) huE
    (fun i j => sub_nonneg.mpr (hDE i j))
  have h₁' := matrix_mul_nonnegative ((u * E⁻¹) * (E-D)) (D⁻¹ * v) h₁ hDv 0 0
  have h₂ := matrix_mul_nonnegative (u-l) (E⁻¹ * v)
    (fun i j => sub_nonneg.mpr (hlu i j)) hEv 0 0
  have h₃ := matrix_mul_nonnegative (l * E⁻¹) (v-c) hlE
    (fun i j => sub_nonneg.mpr (hcv i j)) 0 0
  have hi := congrArg (fun M : Mat 1 => M 0 0)
    (schur_bilinear_difference l u c v D E hD hE)
  simp only [Matrix.sub_apply, Matrix.add_apply] at hi
  linarith

end NLA.IV03

/-
Deterministic good-event consequences for the source derivative bound.

This turns the radial-plus-tail-energy condition appearing in (3.22),
together with the radial cutoff, into a uniform conservative bound for the
polynomial-chart derivative variation.
-/
import NLA.FR05.DerivativeNorm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

/-- The source radial/tail-energy event bounds the conservative row constant
used in the derivative estimate. -/
theorem plantedRowSupEnergy_le_of_radial_tail_bound
    {n : ℕ} (row : PlantedRow n) {δ B : ℝ}
    (hδ : 0 < δ) (hradial : δ ≤ row.radial)
    (henergy : row.radial + squaredEuclideanNorm row.tail ≤ B) :
    plantedRowSupEnergy row ≤ ((n + 2 : ℕ) : ℝ) ^ 2 * B / δ := by
  have htail : 0 ≤ squaredEuclideanNorm row.tail :=
    squaredEuclideanNorm_nonneg row.tail
  have hB : 0 ≤ B :=
    le_trans (add_nonneg row.radial_pos.le htail) henergy
  calc
    plantedRowSupEnergy row ≤ plantedRowEuclideanEnergy row :=
      plantedRowSupEnergy_le_euclideanEnergy row
    _ = ((n + 2 : ℕ) : ℝ) ^ 2 *
          (row.radial + squaredEuclideanNorm row.tail) / row.radial :=
      plantedRowEuclideanEnergy_eq_radial_tail row
    _ ≤ ((n + 2 : ℕ) : ℝ) ^ 2 * B / row.radial := by
      apply div_le_div_of_nonneg_right _ row.radial_pos.le
      exact mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
    _ ≤ ((n + 2 : ℕ) : ℝ) ^ 2 * B / δ := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (sq_nonneg _) hB) hδ hradial

/-- On the same good event, the checked directional derivative variation is
bounded uniformly in the row realization. -/
theorem abs_plantedEquationDirectional_sub_linear_le_of_radial_tail_bound
    {n : ℕ} (row : PlantedRow n) (s σ : ℝ) (b c : ℂ) (z t p q : Signal n)
    {δ B R S : ℝ} (hδ : 0 < δ) (hradial : δ ≤ row.radial)
    (henergy : row.radial + squaredEuclideanNorm row.tail ≤ B)
    (hR : 0 ≤ R) (hbase : factorDirectionSup s b z t ≤ R)
    (hdirection : factorDirectionSup σ c p q ≤ S) :
    |plantedEquationDirectional row s b z t σ c p q -
        plantedEquationLinear row σ c p q| ≤
      2 * (((n + 2 : ℕ) : ℝ) ^ 2 * B / δ) * R * S := by
  calc
    |plantedEquationDirectional row s b z t σ c p q -
        plantedEquationLinear row σ c p q| ≤
        2 * plantedRowSupEnergy row * R * S :=
      abs_plantedEquationDirectional_sub_linear_le_of_sup_le row s σ b c z t p q
        hR hbase hdirection
    _ ≤ 2 * (((n + 2 : ℕ) : ℝ) ^ 2 * B / δ) * R * S := by
      have hrow := plantedRowSupEnergy_le_of_radial_tail_bound row hδ hradial henergy
      have hS : 0 ≤ S :=
        le_trans (factorDirectionSup_nonneg σ c p q) hdirection
      gcongr

end NLA.FR05

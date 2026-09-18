/-
Source-parameter specialization of the deterministic derivative good-event
bound.  The deliberately conservative sup-coordinate estimate grows only as
`M^5`, which is still overwhelmingly dominated by the source's `M^-50`
perturbation scale.
-/
import NLA.FR05.DerivativeGoodEvent
import NLA.FR05.SourceParameters
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

theorem source_tailDimension_add_two {M : ℕ} (hM : 2 ≤ M) :
    sourceTailDimension M + 2 = M := by
  unfold sourceTailDimension
  omega

/-- On the source's radial/tail-energy event, every row has a polynomial
`16 M^5` upper bound for the conservative derivative constant. -/
theorem plantedRowSupEnergy_le_source_bound
    {M : ℕ} (hM : 2 ≤ M) (row : PlantedRow (sourceTailDimension M))
    (hradial : sourceDelta M ≤ row.radial)
    (henergy : row.radial + squaredEuclideanNorm row.tail ≤ 16 * (M : ℝ)) :
    plantedRowSupEnergy row ≤ 16 * (M : ℝ) ^ 5 := by
  have hMone : 1 ≤ M := le_trans (by omega) hM
  have hMreal : 0 < (M : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hMone
  calc
    plantedRowSupEnergy row ≤
        ((sourceTailDimension M + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
          sourceDelta M :=
      plantedRowSupEnergy_le_of_radial_tail_bound row
        (sourceDelta_pos M hMone) hradial henergy
    _ = 16 * (M : ℝ) ^ 5 := by
      rw [show sourceTailDimension M + 2 = M from source_tailDimension_add_two hM]
      unfold sourceDelta
      field_simp [hMreal.ne']

end NLA.FR05

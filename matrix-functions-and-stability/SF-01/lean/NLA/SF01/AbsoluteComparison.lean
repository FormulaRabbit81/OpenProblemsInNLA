/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

The comparison inequality follows from the ordinary finite-sum triangle
inequality. No sign condition on a vector or matrix invertibility is assumed.
-/
import NLA.SF01.ShiftStructure
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma mulVec_row_split {n : ℕ} (A : Square n) (y : Vector n) (i : Fin n) :
    (A *ᵥ y) i = A i i * y i + ∑ j ∈ Finset.univ.erase i, A i j * y j := by
  exact (Finset.add_sum_erase Finset.univ (fun j => A i j * y j)
    (Finset.mem_univ i)).symm

lemma comparison_abs_mulVec_general {n : ℕ} (A : Square n) (y : Vector n) :
    ∀ i, (comparison A *ᵥ (fun j => |y j|)) i ≤ |(A *ᵥ y) i| := by
  intro i
  have hsum : |∑ j ∈ Finset.univ.erase i, A i j * y j| ≤
      ∑ j ∈ Finset.univ.erase i, |A i j| * |y j| := by
    simpa only [abs_mul] using
      Finset.abs_sum_le_sum_abs (fun j => A i j * y j) (Finset.univ.erase i)
  have he : A i i * y i = (A *ᵥ y) i + -(∑ j ∈ Finset.univ.erase i, A i j * y j) := by
    rw [mulVec_row_split]
    ring
  have htri := abs_add_le ((A *ᵥ y) i) (-(∑ j ∈ Finset.univ.erase i, A i j * y j))
  rw [← he, abs_neg, abs_mul] at htri
  rw [comparison_mulVec_row]
  linarith

theorem comparison_abs_mulVec {n : ℕ} (A : Square n) (hA : PositiveDiagonal A)
    (t : ℝ) (ht : 0 ≤ t) (y : Vector n) :
    ∀ i, (shifted (comparison A) t *ᵥ (fun j => |y j|)) i ≤
      |(shifted A t *ᵥ y) i| := by
  rw [← shift_comparison A hA t ht]
  exact comparison_abs_mulVec_general (shifted A t) y

end
end NLA.SF01

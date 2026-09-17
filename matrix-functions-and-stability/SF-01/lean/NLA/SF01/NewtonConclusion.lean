/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

The original Newton sequence, with one finite rational representation per
positive iteration valid uniformly over every dimension and admissible matrix.
-/
import NLA.SF01.NewtonData

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

theorem newton_first {n : ℕ} (hn : 1 ≤ n) (A : Square n)
    (hA : Admissible A) :
    newton A 1 = (1 / 2 : ℝ) • (A + 1) ∧ newton A 1 = ridgeEval initialData A := by
  have hu := (H_positive_weight hn A hA.1).1
  have hi : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hu)
  have hfirst : newton A 1 = (1 / 2 : ℝ) • (A + 1) := by
    simp only [newton, hi]
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  simp [ridgeEval, initialData, smul_add, add_comm]
  exact Finset.sum_eq_zero (fun j _ => Fin.elim0 j)

theorem iterate_ridge_representation (k : ℕ) (hk : 1 ≤ k) :
    ∃ d : RidgeData, ValidData d ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : Square n, Admissible A → newton A k = ridgeEval d A := by
  revert hk
  induction k with
  | zero =>
      intro hk
      omega
  | succ k ih =>
      intro _
      by_cases hkzero : k = 0
      · subst k
        refine ⟨initialData, initial_data_valid, ?_⟩
        intro n hn A hA
        exact (newton_first hn A hA).2
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkzero
        obtain ⟨d, hd, hrep⟩ := ih hkpos
        obtain ⟨d', hd', _, _, hstep⟩ := newton_data_step d hd
        refine ⟨d', hd', ?_⟩
        intro n hn A hA
        rw [newton, hrep n hn A hA, hstep n hn A hA]

theorem canonical_newton_preservation {n : ℕ} (hn : 1 ≤ n) (A : Square n)
    (hH : IsHMatrix A) (hdiag : PositiveDiagonal A) (k : ℕ) :
    IsHMatrix (newton A k) ∧ PositiveDiagonal (newton A k) ∧ IsUnit (newton A k) := by
  cases k with
  | zero =>
      exact ⟨hH, hdiag, (H_positive_weight hn A hH).1⟩
  | succ k =>
      obtain ⟨d, hd, hrep⟩ := iterate_ridge_representation (k + 1) (Nat.succ_pos k)
      rw [hrep n hn A ⟨hH, hdiag⟩]
      obtain ⟨_, _, _, _, _, hadm, hunit⟩ :=
        ridge_comparison_preserver d hd hn A ⟨hH, hdiag⟩
      exact ⟨hadm.1, hadm.2, hunit⟩

end
end NLA.SF01

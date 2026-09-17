/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Nonnegative scalar shifts preserve the original spectral H-matrix predicate
through its already proved positive-weight equivalence. All parameters are symbolic.
-/
import NLA.SF01.HWeight
import NLA.SF01.SpectralMConverse

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma comparison_diagonal {n : ℕ} (A : Square n) (i : Fin n) :
    comparison A i i = |A i i| := by
  simp [comparison]

lemma comparison_offDiagonal {n : ℕ} (A : Square n) (i j : Fin n)
    (hij : i ≠ j) : comparison A i j = -|A i j| := by
  simp [comparison, hij]

lemma comparison_isZ {n : ℕ} (A : Square n) : IsZMatrix (comparison A) := by
  intro i j hij
  rw [comparison_offDiagonal A i j hij]
  exact neg_nonpos.mpr (abs_nonneg (A i j))

lemma shifted_diagonal {n : ℕ} (A : Square n) (t : ℝ) (i : Fin n) :
    shifted A t i i = A i i + t := by
  simp [shifted, Matrix.one_apply]

lemma shifted_offDiagonal {n : ℕ} (A : Square n) (t : ℝ) (i j : Fin n)
    (hij : i ≠ j) : shifted A t i j = A i j := by
  simp [shifted, Matrix.one_apply, hij]

lemma shifted_isZ {n : ℕ} (C : Square n) (hC : IsZMatrix C) (t : ℝ) :
    IsZMatrix (shifted C t) := by
  intro i j hij
  rw [shifted_offDiagonal C t i j hij]
  exact hC i j hij

lemma shifted_positiveDiagonal {n : ℕ} (A : Square n)
    (hA : PositiveDiagonal A) (t : ℝ) (ht : 0 ≤ t) :
    PositiveDiagonal (shifted A t) := by
  intro i
  rw [shifted_diagonal]
  exact lt_of_lt_of_le (hA i) (le_add_of_nonneg_right ht)

lemma shifted_mulVec_apply {n : ℕ} (C : Square n) (t : ℝ)
    (v : Vector n) (i : Fin n) :
    (shifted C t *ᵥ v) i = (C *ᵥ v) i + t * v i := by
  simp only [shifted, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma shifted_positiveWeight {n : ℕ} (C : Square n) (v : Vector n)
    (hv : PositiveWeight C v) (t : ℝ) (ht : 0 ≤ t) :
    PositiveWeight (shifted C t) v := by
  refine ⟨hv.1, ?_⟩
  intro i
  rw [shifted_mulVec_apply]
  exact lt_of_lt_of_le (hv.2 i)
    (le_add_of_nonneg_right (mul_nonneg ht (hv.1 i).le))

theorem shift_comparison {n : ℕ} (A : Square n) (hA : PositiveDiagonal A)
    (t : ℝ) (ht : 0 ≤ t) :
    comparison (shifted A t) = shifted (comparison A) t := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hpos : 0 < A i i + t := lt_of_lt_of_le (hA i) (le_add_of_nonneg_right ht)
    simp only [comparison_diagonal, shifted_diagonal, abs_of_pos (hA i), abs_of_pos hpos]
  · rw [comparison_offDiagonal (shifted A t) i j hij,
      shifted_offDiagonal A t i j hij,
      shifted_offDiagonal (comparison A) t i j hij,
      comparison_offDiagonal A i j hij]

theorem H_shift_structure {n : ℕ} (hn : 1 ≤ n) (A : Square n)
    (hA : Admissible A) (t : ℝ) (ht : 0 ≤ t) :
    Admissible (shifted A t) ∧ IsUnit (shifted A t) ∧
      PositiveWeight (shifted (comparison A) t) (weightVector (comparison A)) := by
  have hbase := H_positive_weight hn A hA.1
  have hw : PositiveWeight (shifted (comparison A) t) (weightVector (comparison A)) :=
    shifted_positiveWeight (comparison A) (weightVector (comparison A)) hbase.2.1 t ht
  have hZ : IsZMatrix (shifted (comparison A) t) := shifted_isZ _ (comparison_isZ A) t
  have hH : IsHMatrix (shifted A t) := by
    change IsSpectralM (comparison (shifted A t))
    rw [shift_comparison A hA.2 t ht]
    exact weighted_Z_spectralM hn _ (weightVector (comparison A)) hZ hw
  have hc : PositiveWeight (comparison (shifted A t)) (weightVector (comparison A)) := by
    rw [shift_comparison A hA.2 t ht]
    exact hw
  exact ⟨⟨hH, shifted_positiveDiagonal A hA.2 t ht⟩,
    weighted_comparison_isUnit (shifted A t) (weightVector (comparison A)) hc, hw⟩

end
end NLA.SF01

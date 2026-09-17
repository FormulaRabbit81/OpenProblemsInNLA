/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Positive weighted row sums for finite rational functions of Z-matrices.
The inverse positivity is supplied by Sidney Holden's attributed IV-03 proof.
-/
import NLA.SF01.RidgeAlgebra
import Mathlib.Tactic

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma entrywiseNonnegative_mulVec {n : ℕ} (B : Square n)
    (hB : EntrywiseNonnegative B) (v : Vector n) (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ (B *ᵥ v) i := by
  intro i
  change 0 ≤ ∑ j : Fin n, B i j * v j
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hB i j) (hv j))

lemma positiveWeight_of_entrywise_le {n : ℕ} (C D : Square n) (v : Vector n)
    (hv : PositiveWeight C v) (hCD : ∀ i j, C i j ≤ D i j) :
    PositiveWeight D v := by
  refine ⟨hv.1, ?_⟩
  intro i
  have hrow : (C *ᵥ v) i ≤ (D *ᵥ v) i := by
    change (∑ j : Fin n, C i j * v j) ≤ ∑ j : Fin n, D i j * v j
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hCD i j) (hv.1 j).le)
  exact lt_of_lt_of_le (hv.2 i) hrow

lemma weightedZ_positiveDiagonal {n : ℕ} (C : Square n) (v : Vector n)
    (hZ : IsZMatrix C) (hv : PositiveWeight C v) : PositiveDiagonal C := by
  intro i
  have hoff : (∑ j ∈ Finset.univ.erase i, C i j * v j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonpos_of_nonneg
      (hZ i j (Finset.mem_erase.mp hj).1.symm) (hv.1 j).le
  have hprod : 0 < C i i * v i := by
    have hrow := hv.2 i
    rw [mulVec_row_split] at hrow
    linarith
  exact (mul_pos_iff_of_pos_right (hv.1 i)).mp hprod

lemma weightedZ_resolvent_part {n : ℕ} (C : Square n) (v : Vector n)
    (hZ : IsZMatrix C) (hv : PositiveWeight C v) (t : ℝ) (ht : 0 ≤ t) :
    IsZMatrix (C * (shifted C t)⁻¹) ∧
      ∀ i, 0 ≤ ((C * (shifted C t)⁻¹) *ᵥ v) i := by
  have hshiftZ := shifted_isZ C hZ t
  have hshiftv := shifted_positiveWeight C v hv t ht
  have hunit := weightedZ_isUnit (shifted C t) v hshiftZ hshiftv
  have hnonneg := weightedZ_inverse_nonnegative (shifted C t) v hshiftZ hshiftv
  refine ⟨?_, ?_⟩
  · intro i j hij
    rw [shifted_right_resolvent C t hunit]
    change (1 : Square n) i j - t * ((shifted C t)⁻¹) i j ≤ 0
    rw [Matrix.one_apply_ne hij, zero_sub]
    exact neg_nonpos.mpr (mul_nonneg ht (hnonneg i j))
  · intro i
    rw [shifted_inverse_commutation C t hunit, ← Matrix.mulVec_mulVec]
    exact entrywiseNonnegative_mulVec (shifted C t)⁻¹ hnonneg (C *ᵥ v)
      (fun j => (hv.2 j).le) i

lemma weightedZ_ridge {n : ℕ} (d : RidgeData) (hd : ValidData d)
    (C : Square n) (v : Vector n) (hZ : IsZMatrix C) (hv : PositiveWeight C v) :
    IsZMatrix (ridgeEval d C) ∧ PositiveWeight (ridgeEval d C) v := by
  have hparts : ∀ k : Fin d.size,
      IsZMatrix (C * (shifted C (d.poles k))⁻¹) ∧
        ∀ i, 0 ≤ ((C * (shifted C (d.poles k))⁻¹) *ᵥ v) i := by
    intro k
    exact weightedZ_resolvent_part C v hZ hv (d.poles k) (hd.2.2.1 k).le
  refine ⟨?_, hv.1, ?_⟩
  · intro i j hij
    rw [ridgeEval_apply, Matrix.one_apply_ne hij, mul_zero, zero_add]
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hd.2.1.le (hZ i j hij))
      (Finset.sum_nonpos (fun k _ => mul_nonpos_of_nonneg_of_nonpos
        (hd.2.2.2 k) ((hparts k).1 i j hij)))
  · intro i
    rw [ridgeEval_mulVec_apply]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (mul_pos hd.1 (hv.1 i))
        (mul_nonneg hd.2.1.le (hv.2 i).le))
      (Finset.sum_nonneg (fun k _ => mul_nonneg (hd.2.2.2 k) ((hparts k).2 i)))

end
end NLA.SF01

/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted formalization of Colbrook's genuine principal inverse-M closure.
All block invertibility is derived from the original inverse-M hypothesis. -/
import NLA.IV03.Proof
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma inverseM_principal_split {m r n : ℕ} {A : Mat n} (hA : IsInverseM A)
    (q : (Fin m ⊕ Fin r) ≃ Fin n) :
    IsInverseM (A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inl i))) := by
  let e : Fin m ↪ Fin n := ⟨fun i => q (Sum.inl i),
    fun _ _ h => Sum.inl_injective (q.injective h)⟩
  let g : Fin r ↪ Fin n := ⟨fun i => q (Sum.inr i),
    fun _ _ h => Sum.inr_injective (q.injective h)⟩
  let P := (A⁻¹).submatrix e e
  let Q := (A⁻¹).submatrix e g
  let R := (A⁻¹).submatrix g e
  let D := (A⁻¹).submatrix g g
  have hblock : fromBlocks P Q R D = (A⁻¹).submatrix q q := by
    ext i j
    cases i <;> cases j <;> rfl
  have hD := inverseM_inverse_principal hA g
  have hH : IsUnit (fromBlocks P Q R D) := by
    rw [hblock, Matrix.isUnit_submatrix_equiv]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hA.1
  letI : Invertible D := hD.1.invertible
  letI : Invertible (fromBlocks P Q R D) := hH.invertible
  letI : Invertible (P - Q * ⅟D * R) :=
    Matrix.invertibleOfFromBlocks₂₂Invertible P Q R D
  have hK : IsUnit (P - Q * D⁻¹ * R) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using
      (isUnit_of_invertible (P - Q * ⅟D * R))
  have hb := Matrix.invOf_fromBlocks₂₂_eq P Q R D
  simp only [Matrix.invOf_eq_nonsing_inv] at hb
  have he : A.submatrix e e = (P - Q * D⁻¹ * R)⁻¹ := by
    have hh := congrArg (fun M : Matrix (Fin m ⊕ Fin r) (Fin m ⊕ Fin r) ℝ =>
      M.submatrix Sum.inl Sum.inl) hb
    rw [hblock, Matrix.inv_submatrix_equiv, Matrix.nonsing_inv_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.1)] at hh
    exact hh
  have hz : ∀ i j, i ≠ j → (P - Q * D⁻¹ * R) i j ≤ 0 := by
    apply zMatrix_schur_offdiagonal P Q R D
    · intro i j hij
      exact hA.2.2 (e i) (e j) (fun h => hij (e.injective h))
    · intro i j
      apply hA.2.2
      intro h
      have hh := q.injective h
      cases hh
    · intro i j
      apply hA.2.2
      intro h
      have hh := q.injective h
      cases hh
    · exact hD.2.2
  change IsInverseM (A.submatrix e e)
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hK
  · intro i j
    exact hA.2.1 (e i) (e j)
  · rw [he, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hK)]
    exact hz

/-- Principal inverse-M closure for an arbitrary finite index embedding.
The complement is enumerated only to apply the genuine block inverse identity. -/
lemma inverseM_principal {m n : ℕ} {A : Mat n} (hA : IsInverseM A)
    (e : Fin m ↪ Fin n) : IsInverseM (A.submatrix e e) := by
  let T := {j : Fin n // j ∉ Set.range e}
  let f : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let q : (Fin m ⊕ Fin (Fintype.card T)) ≃ Fin n :=
    ((Equiv.ofInjective e e.injective).sumCongr f).trans
      (Equiv.sumCompl (fun j : Fin n => j ∈ Set.range e))
  have he : (fun i : Fin m => q (Sum.inl i)) = e := by
    funext i
    rfl
  simpa only [he] using inverseM_principal_split hA q

lemma inverseM_principal_det_pos {m n : ℕ} {A : Mat n} (hA : IsInverseM A)
    (e : Fin m ↪ Fin n) : 0 < (A.submatrix e e).det :=
  inverseM_det_pos (inverseM_principal hA e)

/-- Every principal Schur complement is inverse-M. Invertibility of the
eliminated block and the Schur complement follows from principal closure. -/
lemma inverseM_schur_split {m r n : ℕ} {A : Mat n} (hA : IsInverseM A)
    (q : (Fin m ⊕ Fin r) ≃ Fin n) :
    IsInverseM (A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inl i)) -
      A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inr i)) *
      (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))⁻¹ *
      A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inl i))) := by
  let e : Fin m ↪ Fin n := ⟨fun i => q (Sum.inl i),
    fun _ _ h => Sum.inl_injective (q.injective h)⟩
  let g : Fin r ↪ Fin n := ⟨fun i => q (Sum.inr i),
    fun _ _ h => Sum.inr_injective (q.injective h)⟩
  let P := A.submatrix e e
  let Q := A.submatrix e g
  let R := A.submatrix g e
  let D := A.submatrix g g
  have hblock : fromBlocks P Q R D = A.submatrix q q := by
    ext i j
    cases i <;> cases j <;> rfl
  have hD := inverseM_principal hA g
  have hH : IsUnit (fromBlocks P Q R D) := by
    rw [hblock, Matrix.isUnit_submatrix_equiv]
    exact hA.1
  letI : Invertible D := hD.1.invertible
  letI : Invertible (fromBlocks P Q R D) := hH.invertible
  letI : Invertible (P - Q * ⅟D * R) :=
    Matrix.invertibleOfFromBlocks₂₂Invertible P Q R D
  have hK : IsUnit (P - Q * D⁻¹ * R) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using
      (isUnit_of_invertible (P - Q * ⅟D * R))
  have hb := Matrix.invOf_fromBlocks₂₂_eq P Q R D
  simp only [Matrix.invOf_eq_nonsing_inv] at hb
  have he : (A⁻¹).submatrix e e = (P - Q * D⁻¹ * R)⁻¹ := by
    have hh := congrArg (fun M : Matrix (Fin m ⊕ Fin r) (Fin m ⊕ Fin r) ℝ =>
      M.submatrix Sum.inl Sum.inl) hb
    rw [hblock, Matrix.inv_submatrix_equiv] at hh
    exact hh
  have hinv : P - Q * D⁻¹ * R = ((A⁻¹).submatrix e e)⁻¹ := by
    rw [he, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hK)]
  change IsInverseM (P - Q * D⁻¹ * R)
  refine ⟨hK, ?_, ?_⟩
  · rw [hinv]
    exact (inverseM_inverse_principal hA e).2.2
  · rw [← he]
    intro i j hij
    exact hA.2.2 (e i) (e j) (fun h => hij (e.injective h))

/-- The transfer block used in the Schur derivative has nonnegative entries.
This follows from the actual inverse block equations, without a sign premise
on the transfer block itself. -/
lemma inverseM_cross_transfer_nonnegative {m r n : ℕ} {A : Mat n}
    (hA : IsInverseM A) (q : (Fin m ⊕ Fin r) ≃ Fin n) :
    ∀ i j, 0 ≤ (A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inr i)) *
      (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))⁻¹) i j := by
  let e : Fin m ↪ Fin n := ⟨fun i => q (Sum.inl i),
    fun _ _ h => Sum.inl_injective (q.injective h)⟩
  let g : Fin r ↪ Fin n := ⟨fun i => q (Sum.inr i),
    fun _ _ h => Sum.inr_injective (q.injective h)⟩
  let P := A.submatrix e e
  let Q := A.submatrix e g
  let R := A.submatrix g e
  let D := A.submatrix g g
  let E := (A⁻¹).submatrix e e
  let F := (A⁻¹).submatrix e g
  let G := (A⁻¹).submatrix g e
  let H := (A⁻¹).submatrix g g
  have hblock : fromBlocks P Q R D = A.submatrix q q := by
    ext i j; cases i <;> cases j <;> rfl
  have hiblock : fromBlocks E F G H = (A⁻¹).submatrix q q := by
    ext i j; cases i <;> cases j <;> rfl
  have hprod : fromBlocks E F G H * fromBlocks P Q R D = 1 := by
    rw [hiblock, hblock, ← Matrix.inv_submatrix_equiv]
    apply Matrix.nonsing_inv_mul
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    simpa using hA.1
  rw [Matrix.fromBlocks_multiply] at hprod
  have hrel : E * Q + F * D = 0 := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin m ⊕ Fin r) (Fin m ⊕ Fin r) ℝ =>
      M (Sum.inl i) (Sum.inr j)) hprod
    simpa [Matrix.fromBlocks, Matrix.one_apply] using hh
  have hD := inverseM_principal hA g
  have hE := inverseM_inverse_principal hA e
  have heq : Q * D⁻¹ = -(E⁻¹ * F) := by
    have hh := congrArg (fun M => E⁻¹ * M * D⁻¹) hrel
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul E
        ((Matrix.isUnit_iff_isUnit_det _).mp hE.1), Matrix.one_mul] at hh
    have hdd : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D
      ((Matrix.isUnit_iff_isUnit_det _).mp hD.1)
    have hassoc : E⁻¹ * F * D * D⁻¹ = E⁻¹ * F := by
      rw [Matrix.mul_assoc, hdd, Matrix.mul_one]
    rw [hassoc] at hh
    exact eq_neg_of_add_eq_zero_left hh
  change ∀ i j, 0 ≤ (Q * D⁻¹) i j
  rw [heq]
  intro i j
  change 0 ≤ -((E⁻¹ * F) i j)
  apply neg_nonneg.mpr
  rw [Matrix.mul_apply]
  apply Finset.sum_nonpos
  intro k _
  apply mul_nonpos_of_nonneg_of_nonpos (hE.2.2 i k)
  apply hA.2.2
  intro h
  have hh := q.injective h
  cases hh

lemma inverseM_transpose {n : ℕ} {A : Mat n} (hA : IsInverseM A) :
    IsInverseM Aᵀ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using hA.1
  · intro i j
    exact hA.2.1 j i
  · rw [← Matrix.transpose_nonsing_inv]
    intro i j hij
    exact hA.2.2 j i (Ne.symm hij)

lemma inverseM_left_transfer_nonnegative {m r n : ℕ} {A : Mat n}
    (hA : IsInverseM A) (q : (Fin m ⊕ Fin r) ≃ Fin n) :
    ∀ i j, 0 ≤ ((A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))⁻¹ *
      A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inl i))) i j := by
  intro i j
  have h := inverseM_cross_transfer_nonnegative (inverseM_transpose hA) q j i
  have ht : (Aᵀ).submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)) =
      (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))ᵀ := rfl
  rw [ht, ← Matrix.transpose_nonsing_inv] at h
  have hc : (Aᵀ).submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inr i)) =
      (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inl i)))ᵀ := rfl
  rw [hc, ← Matrix.transpose_mul] at h
  exact h

end NLA.IV03

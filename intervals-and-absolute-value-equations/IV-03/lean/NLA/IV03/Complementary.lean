/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted formalization of the complementary principal minor identity.
The invertibility hypotheses are stated explicitly; later applications derive
them from the proper principal minor assumptions. -/
import NLA.IV03.Principal
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma complementary_principal_minor_split {m r n : ℕ} (A : Mat n)
    (q : (Fin m ⊕ Fin r) ≃ Fin n) (hA : IsUnit A)
    (hD : IsUnit (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))) :
    ((A⁻¹).submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inl i))).det * A.det =
      (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i))).det := by
  let e := fun i : Fin m => q (Sum.inl i)
  let g := fun i : Fin r => q (Sum.inr i)
  let P := A.submatrix e e
  let Q := A.submatrix e g
  let R := A.submatrix g e
  let D := A.submatrix g g
  have hblock : fromBlocks P Q R D = A.submatrix q q := by
    ext i j; cases i <;> cases j <;> rfl
  have hH : IsUnit (fromBlocks P Q R D) := by
    rw [hblock, Matrix.isUnit_submatrix_equiv]
    exact hA
  letI : Invertible D := hD.invertible
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
  have hd := Matrix.det_fromBlocks₂₂ P Q R D
  rw [hblock, Matrix.det_submatrix_equiv_self] at hd
  simp only [Matrix.invOf_eq_nonsing_inv] at hd
  change ((A⁻¹).submatrix e e).det * A.det = D.det
  rw [he, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hd]
  have hn : (P - Q * D⁻¹ * R).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hK).ne_zero
  field_simp

/-- Under a negative determinant, every nonempty inverse principal minor is
negative if all proper principal minors of the original matrix are positive.
This is derived from the complementary-minor identity above. -/
lemma inverse_principal_det_neg {n k : ℕ} (A : Mat n) (hk : 0 < k)
    (e : Fin k ↪ Fin n) (hA : A.det < 0)
    (hp : ∀ m, m < n → ∀ f : Fin m ↪ Fin n, 0 < (A.submatrix f f).det) :
    ((A⁻¹).submatrix e e).det < 0 := by
  let T := {j : Fin n // j ∉ Set.range e}
  let f : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let q : (Fin k ⊕ Fin (Fintype.card T)) ≃ Fin n :=
    ((Equiv.ofInjective e e.injective).sumCongr f).trans
      (Equiv.sumCompl (fun j : Fin n => j ∈ Set.range e))
  let g : Fin (Fintype.card T) ↪ Fin n := ⟨fun i => q (Sum.inr i),
    fun _ _ h => Sum.inr_injective (q.injective h)⟩
  have he : (fun i : Fin k => q (Sum.inl i)) = e := by funext i; rfl
  have hcard := Fintype.card_congr q
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hg : Fintype.card T < n := by omega
  have hD := hp _ hg g
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (ne_of_lt hA))
  have hDu : IsUnit (A.submatrix g g) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (ne_of_gt hD))
  have hi := complementary_principal_minor_split A q hu hDu
  rw [he] at hi
  change ((A⁻¹).submatrix e e).det * A.det = (A.submatrix g g).det at hi
  nlinarith

end NLA.IV03

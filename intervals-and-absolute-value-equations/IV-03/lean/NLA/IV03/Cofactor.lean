/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted formalization of the Schur/cofactor identity without regularity. -/
import NLA.IV03.Adjugate
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma adjugate_fromBlocks_two_offdiag {r : ℕ} (P : Mat 2)
    (Q : Matrix (Fin 2) (Fin r) ℝ) (R : Matrix (Fin r) (Fin 2) ℝ)
    (D : Mat r) (hD : IsUnit D) :
    (fromBlocks P Q R D).adjugate (Sum.inl 0) (Sum.inl 1) =
      -D.det * (P - Q * D⁻¹ * R) 0 1 := by
  let P' := P.updateRow 1 ![1,0]
  let Q' := Q.updateRow 1 0
  have hrow : (fromBlocks P Q R D).updateRow (Sum.inl 1)
      (Pi.single (Sum.inl 0) 1) = fromBlocks P' Q' R D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;>
          simp [P', Q', Matrix.updateRow_apply, Matrix.fromBlocks, Pi.single_apply]
      | inr j => fin_cases i <;>
          simp [P', Q', Matrix.updateRow_apply, Matrix.fromBlocks, Pi.single_apply]
    | inr i => cases j <;>
        simp [Matrix.updateRow_apply, Matrix.fromBlocks, Pi.single_apply]
  letI : Invertible D := hD.invertible
  rw [Matrix.adjugate_apply, hrow, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  have hschur : P' - Q' * D⁻¹ * R = (P - Q * D⁻¹ * R).updateRow 1 ![1,0] := by
    ext i j
    fin_cases i <;>
      simp [P', Q', Matrix.updateRow_apply, Matrix.mul_apply]
  rw [hschur, Matrix.det_fin_two]
  simp [Matrix.updateRow_apply]
  ring

lemma adjugate_two_schur_split {r n : ℕ} (A : Mat n)
    (q : (Fin 2 ⊕ Fin r) ≃ Fin n)
    (hD : IsUnit (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))) :
    A.adjugate (q (Sum.inl 0)) (q (Sum.inl 1)) =
      -(A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i))).det *
      (A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inl i)) -
        A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inr i)) *
        (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))⁻¹ *
        A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inl i))) 0 1 := by
  let e := fun i : Fin 2 => q (Sum.inl i)
  let g := fun i : Fin r => q (Sum.inr i)
  have hblock : fromBlocks (A.submatrix e e) (A.submatrix e g)
      (A.submatrix g e) (A.submatrix g g) = A.submatrix q q := by
    ext i j; cases i <;> cases j <;> rfl
  have hi := adjugate_fromBlocks_two_offdiag (A.submatrix e e)
    (A.submatrix e g) (A.submatrix g e) (A.submatrix g g) hD
  rw [hblock, Matrix.adjugate_submatrix_equiv_self] at hi
  exact hi

end NLA.IV03

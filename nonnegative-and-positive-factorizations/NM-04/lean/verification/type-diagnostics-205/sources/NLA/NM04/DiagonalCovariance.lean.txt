/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Mathematical source: Matthew J. Colbrook's
NM-04 manuscript, diagonal covariance step. No positivity or invertibility is
needed for the two covariance identities, including empty selected minors.
-/
import NLA.NM04.Definitions
import Mathlib.Algebra.BigOperators.Fin
import LeanCert.Tactic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix

private lemma selected_product {α : Type*} [LinearOrder α] (U : Finset α)
    {k : ℕ} (h : U.card = k) (f : α → ℝ) :
    (∏ i : Fin k, f (U.orderEmbOfFin h i)) = ∏ i ∈ U, f i := by
  classical
  calc
    (∏ i : Fin k, f (U.orderEmbOfFin h i)) =
        ∏ i ∈ Finset.univ.map (U.orderEmbOfFin h).toEmbedding, f i := by
      rw [Finset.prod_map]
      rfl
    _ = _ := by rw [U.map_orderEmbOfFin_univ h]

private lemma scaled_det {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D ℝ) (a b : D → ℝ) :
    Matrix.det (fun i j => a i * M i j * b j) = (∏ i, a i) * (∏ j, b j) * M.det := by
  have h : (fun i j => a i * M i j * b j) =
      Matrix.of (fun i j => a i * (Matrix.of (fun i j => b j * M i j)) i j) := by
    funext i j
    simp only [Matrix.of_apply]
    ring
  rw [h, Matrix.det_mul_column, Matrix.det_mul_row]
  ring

private lemma scaled_minor {α β : Type*} [LinearOrder α] [LinearOrder β]
    (T : Matrix α β ℝ) (a : α → ℝ) (b : β → ℝ) (I : MinorIndex α β) :
    minor (fun i j => a i * T i j * b j) I =
      (∏ i ∈ I.1.1, a i) * (∏ j ∈ I.1.2, b j) * minor T I := by
  have h := scaled_det (minorMatrix T I)
    (fun i => a (I.1.1.orderEmbOfFin rfl i))
    (fun j => b (I.1.2.orderEmbOfFin I.property.symm j))
  rw [selected_product, selected_product] at h
  exact h

theorem diagonal_minor_covariance {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ) (I : Index m n) :
    delta (diagonalScale A a b) hm hn I = covarianceFactor a b hm hn I * delta A hm hn I ∧
    gamma (diagonalScale A a b) hm hn I = covarianceFactor a b hm hn I * gamma A hm hn I := by
  constructor
  · let rows : Fin (I.1.1.card + 1) → Fin m := Fin.cons (firstIndex hm)
      (fun i => (I.1.1.orderEmbOfFin rfl i).val)
    let cols : Fin (I.1.1.card + 1) → Fin n := Fin.cons (firstIndex hn)
      (fun j => (I.1.2.orderEmbOfFin I.property.symm j).val)
    change Matrix.det (fun i j => a (rows i) * A (rows i) (cols j) * b (cols j)) =
      covarianceFactor a b hm hn I * (A.submatrix rows cols).det
    refine (scaled_det (A.submatrix rows cols)
      (fun i => a (rows i)) (fun j => b (cols j))).trans ?_
    have hr : (∏ i, a (rows i)) = a (firstIndex hm) * ∏ i ∈ I.1.1, a i.val := by
      rw [Fin.prod_univ_succ]
      simp only [rows, Fin.cons_zero, Fin.cons_succ]
      rw [selected_product I.1.1 rfl (fun i => a i.val)]
    have hc : (∏ j, b (cols j)) = b (firstIndex hn) * ∏ j ∈ I.1.2, b j.val := by
      rw [Fin.prod_univ_succ]
      simp only [cols, Fin.cons_zero, Fin.cons_succ]
      rw [selected_product I.1.2 I.property.symm (fun j => b j.val)]
    rw [hr, hc]
    unfold covarianceFactor
    ring
  · unfold gamma
    have ht : minor (tailMatrix (diagonalScale A a b)) I =
        (∏ i ∈ I.1.1, a i.val) * (∏ j ∈ I.1.2, b j.val) * minor (tailMatrix A) I :=
      scaled_minor (tailMatrix A) (fun i => a i.val) (fun j => b j.val) I
    rw [ht]
    simp only [diagonalScale, covarianceFactor]
    ring

theorem diagonal_pencil_covariance {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ) (z : ℝ) :
    pencil (diagonalScale A a b) hm hn z =
      pencil A hm hn z * Matrix.diagonal (covarianceFactor a b hm hn) := by
  classical
  have hd : delta (diagonalScale A a b) hm hn =
      fun I => covarianceFactor a b hm hn I * delta A hm hn I :=
    funext (fun I => (diagonal_minor_covariance hm hn A a b I).1)
  have hg : gamma (diagonalScale A a b) hm hn =
      fun I => covarianceFactor a b hm hn I * gamma A hm hn I :=
    funext (fun I => (diagonal_minor_covariance hm hn A a b I).2)
  ext I J
  simp only [pencil, hd, hg, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal]
  by_cases h : I = J
  · subst J
    simp only [Matrix.diagonal_apply_eq]
    ring
  · simp only [Matrix.diagonal_apply_ne _ h]
    ring

#print axioms diagonal_minor_covariance
#print axioms diagonal_pencil_covariance
#assert_trust kernel diagonal_minor_covariance
#assert_trust kernel diagonal_pencil_covariance

end
end NLA.NM04

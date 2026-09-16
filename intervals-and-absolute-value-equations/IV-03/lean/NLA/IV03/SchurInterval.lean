/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted full-box Schur comparison using proper principal inverse-M blocks. -/
import NLA.IV03.IntervalStructure
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma interval_schur_nonnegative {r n : ℕ} (L U A : Mat n)
    (hLU : OrderedEndpoints L U) (hA : A ∈ intervalFamily L U)
    (q : (Fin 2 ⊕ Fin r) ≃ Fin n)
    (hp : ∀ X ∈ intervalFamily L U, ∀ m, m < n →
      ∀ e : Fin m ↪ Fin n, IsInverseM (X.submatrix e e))
    (hV : IsInverseM (vertex L U (-1) (q (Sum.inl 0)) (q (Sum.inl 1)))) :
    0 ≤ (A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inl i)) -
      A.submatrix (fun i => q (Sum.inl i)) (fun i => q (Sum.inr i)) *
      (A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inr i)))⁻¹ *
      A.submatrix (fun i => q (Sum.inr i)) (fun i => q (Sum.inl i))) 0 1 := by
  let g : Fin r ↪ Fin n := ⟨fun k => q (Sum.inr k),
    fun _ _ h => Sum.inr_injective (q.injective h)⟩
  have hg : ∀ k, g k = q (Sum.inr k) := fun _ => rfl
  let l : Matrix (Fin 1) (Fin r) ℝ := A.submatrix (fun _ => q (Sum.inl 0)) g
  let u : Matrix (Fin 1) (Fin r) ℝ := U.submatrix (fun _ => q (Sum.inl 0)) g
  let c : Matrix (Fin r) (Fin 1) ℝ := A.submatrix g (fun _ => q (Sum.inl 1))
  let v : Matrix (Fin r) (Fin 1) ℝ := U.submatrix g (fun _ => q (Sum.inl 1))
  let D := L.submatrix g g
  let E := A.submatrix g g
  let X : Mat n := fun k t => if k = q (Sum.inl 0) then U k t else A k t
  let Y : Mat n := fun k t => if t = q (Sum.inl 1) then U k t else A k t
  let Z : Mat n := fun k t => if t = q (Sum.inl 1) then U k t else L k t
  have hL : L ∈ intervalFamily L U := fun i j => ⟨le_rfl, hLU i j⟩
  have hX : X ∈ intervalFamily L U := by
    intro i j
    dsimp [X]
    split_ifs
    · exact ⟨hLU i j, le_rfl⟩
    · exact hA i j
  have hY : Y ∈ intervalFamily L U := by
    intro i j
    dsimp [Y]
    split_ifs
    · exact ⟨hLU i j, le_rfl⟩
    · exact hA i j
  have hZ : Z ∈ intervalFamily L U := by
    intro i j
    dsimp [Z]
    split_ifs
    · exact ⟨hLU i j, le_rfl⟩
    · exact hL i j
  have huE : ∀ i j, 0 ≤ (u * E⁻¹) i j := by
    have h := (proper_principal_transfer X q (hp X hX) 0).1
    simpa [X, u, E, hg, Matrix.submatrix, q.injective.eq_iff] using h
  have hlE : ∀ i j, 0 ≤ (l * E⁻¹) i j := by
    exact (proper_principal_transfer A q (hp A hA) 0).1
  have hEv : ∀ i j, 0 ≤ (E⁻¹ * v) i j := by
    have h := (proper_principal_transfer Y q (hp Y hY) 1).2
    simpa [Y, v, E, hg, Matrix.submatrix, q.injective.eq_iff] using h
  have hDv : ∀ i j, 0 ≤ (D⁻¹ * v) i j := by
    have h := (proper_principal_transfer Z q (hp Z hZ) 1).2
    simpa [Z, v, D, hg, Matrix.submatrix, q.injective.eq_iff] using h
  have hcard := Fintype.card_congr q
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hr : r < n := by omega
  have hD : IsUnit D := (hp L hL r hr g).1
  have hE : IsUnit E := (hp A hA r hr g).1
  have hcomp := schur_bilinear_monotone l u c v D E hD hE
    (fun i j => (hA _ _).2) (fun i j => (hA _ _).2)
    (fun i j => (hA _ _).1) huE hDv hEv hlE
  have vertexEntry (i j k t : Fin n) : vertex L U (-1) i j k t =
      if (k = i ↔ t = j) then L k t else U k t := by
    by_cases hk : k = i <;> by_cases ht : t = j <;>
      simp [vertex, center, radius, signVector, hk, ht] <;> ring
  have hbase : 0 ≤ L (q (Sum.inl 0)) (q (Sum.inl 1)) - (u * D⁻¹ * v) 0 0 := by
    have hs := (inverseM_schur_split hV q).2.1 0 1
    simpa [vertexEntry, u, v, D, hg, Matrix.submatrix, Matrix.mul_apply, q.injective.eq_iff] using hs
  change 0 ≤ A (q (Sum.inl 0)) (q (Sum.inl 1)) - (l * E⁻¹ * c) 0 0
  have he := (hA (q (Sum.inl 0)) (q (Sum.inl 1))).1
  linarith

end NLA.IV03

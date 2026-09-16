/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted interval/principal-submatrix compatibility for IV-03. -/
import NLA.IV03.Monotonicity
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma vertex_principal {m n : ℕ} (L U : Mat n) (e : Fin m ↪ Fin n)
    (s : ℝ) (i j : Fin m) :
    (vertex L U s (e i) (e j)).submatrix e e =
      vertex (L.submatrix e e) (U.submatrix e e) s i j := by
  ext k l
  simp [vertex, center, radius, signVector, e.injective.eq_iff]

lemma interval_principal {m n : ℕ} {L U A : Mat n}
    (hA : A ∈ intervalFamily L U) (e : Fin m ↪ Fin n) :
    A.submatrix e e ∈ intervalFamily (L.submatrix e e) (U.submatrix e e) := by
  intro i j
  exact hA (e i) (e j)

/-- Transfer signs from a proper principal block containing one retained
index and the eliminated indices. -/
lemma proper_principal_transfer {r n : ℕ} (A : Mat n)
    (q : (Fin 2 ⊕ Fin r) ≃ Fin n)
    (hp : ∀ m, m < n → ∀ e : Fin m ↪ Fin n, IsInverseM (A.submatrix e e))
    (a : Fin 2) :
    (∀ i j, 0 ≤ (A.submatrix (fun _ : Fin 1 => q (Sum.inl a))
      (fun k => q (Sum.inr k)) *
      (A.submatrix (fun k => q (Sum.inr k)) (fun k => q (Sum.inr k)))⁻¹) i j) ∧
    (∀ i j, 0 ≤ ((A.submatrix (fun k => q (Sum.inr k)) (fun k => q (Sum.inr k)))⁻¹ *
      A.submatrix (fun k => q (Sum.inr k)) (fun _ : Fin 1 => q (Sum.inl a))) i j) := by
  let f : (Fin 1 ⊕ Fin r) ↪ Fin n := ⟨Sum.elim (fun _ => q (Sum.inl a))
    (fun k => q (Sum.inr k)), by
      intro i j h
      cases i with
      | inl i => cases j with
        | inl j => congr 1; exact Subsingleton.elim i j
        | inr j => have hh := q.injective h; cases hh
      | inr i => cases j with
        | inl j => have hh := q.injective h; cases hh
        | inr j => congr 1; exact Sum.inr_injective (q.injective h)⟩
  let e : Fin (1+r) ↪ Fin n := finSumFinEquiv.symm.toEmbedding.trans f
  have heL : (fun i : Fin 1 => e (finSumFinEquiv (Sum.inl i))) =
      (fun _ : Fin 1 => q (Sum.inl a)) := by
    funext i
    simp [e, f]
    rfl
  have heR : (fun i : Fin r => e (finSumFinEquiv (Sum.inr i))) =
      (fun k => q (Sum.inr k)) := by
    funext i
    simp [e, f]
    rfl
  have hcard := Fintype.card_congr q
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hsmall : 1+r < n := by omega
  have hA := hp (1+r) hsmall e
  have h₁ := inverseM_cross_transfer_nonnegative hA
    (finSumFinEquiv : Fin 1 ⊕ Fin r ≃ Fin (1+r))
  have h₂ := inverseM_left_transfer_nonnegative hA
    (finSumFinEquiv : Fin 1 ⊕ Fin r ≃ Fin (1+r))
  simp only [Matrix.submatrix_submatrix, Function.comp_def] at h₁ h₂
  rw [heL, heR] at h₁ h₂
  exact ⟨h₁, h₂⟩

end NLA.IV03

/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted interval induction retaining the original full vertex target. -/
import NLA.IV03.SchurInterval
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma interval_adjugate_nonpositive {n : ℕ} (L U A : Mat n)
    (hLU : OrderedEndpoints L U) (hA : A ∈ intervalFamily L U)
    (hp : ∀ X ∈ intervalFamily L U, ∀ m, m < n →
      ∀ e : Fin m ↪ Fin n, IsInverseM (X.submatrix e e))
    (hV : ∀ i j, IsInverseM (vertex L U (-1) i j)) :
    ∀ i j, i ≠ j → A.adjugate i j ≤ 0 := by
  intro i j hij
  let e : Fin 2 ↪ Fin n := ⟨![i,j], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩
  let T := {k : Fin n // k ∉ Set.range e}
  let f : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let q : (Fin 2 ⊕ Fin (Fintype.card T)) ≃ Fin n :=
    ((Equiv.ofInjective e e.injective).sumCongr f).trans
      (Equiv.sumCompl (fun k : Fin n => k ∈ Set.range e))
  let g : Fin (Fintype.card T) ↪ Fin n := ⟨fun k => q (Sum.inr k),
    fun _ _ h => Sum.inr_injective (q.injective h)⟩
  have hq0 : q (Sum.inl 0) = i := rfl
  have hq1 : q (Sum.inl 1) = j := rfl
  have hcard := Fintype.card_congr q
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hr : Fintype.card T < n := by omega
  have hD := hp A hA _ hr g
  have hd := inverseM_det_pos hD
  have hs := interval_schur_nonnegative L U A hLU hA q hp (hV _ _)
  have hi := adjugate_two_schur_split A q hD.1
  rw [hq0, hq1] at hi
  rw [hi]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hd)) hs

lemma inverseM_empty (A : Mat 0) : IsInverseM A := by
  refine ⟨?_, ?_, ?_⟩
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simp
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

end NLA.IV03

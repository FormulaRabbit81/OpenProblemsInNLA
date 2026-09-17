/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted interval induction retaining the original full vertex target. -/
import NLA.IV03.IntervalAdjugate
import NLA.IV03.Vertices
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma interval_inverseM_from_vertices : ∀ n : ℕ, 1 ≤ n →
    ∀ L U : Mat n, OrderedEndpoints L U →
    (∀ i j, IsInverseM (vertex L U (-1) i j)) →
    ∀ A ∈ intervalFamily L U, IsInverseM A := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn L U hLU hv A hA
    by_cases hn1 : n = 1
    · subst n
      exact interval_inverseM_one L U hLU hv A hA
    by_cases hn2 : n = 2
    · subst n
      exact interval_inverseM_two L U hLU hv A hA
    have hp : ∀ X ∈ intervalFamily L U, ∀ m, m < n →
        ∀ e : Fin m ↪ Fin n, IsInverseM (X.submatrix e e) := by
      intro X hX m hm e
      by_cases hm0 : m = 0
      · subst m
        exact inverseM_empty _
      apply ih m hm (by omega) (L.submatrix e e) (U.submatrix e e)
        (fun i j => hLU (e i) (e j))
      · intro i j
        rw [← vertex_principal]
        exact inverseM_principal (hv (e i) (e j)) e
      · exact interval_principal hX e
    have hnn : ∀ i j, 0 ≤ A i j := fun i j =>
      le_trans (lower_nonnegative_of_vertices L U hv i j) (hA i j).1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    apply inverseM_of_proper_principal_and_adjugate (by omega) A hnn
    · intro m hm e
      exact inverseM_det_pos (hp A hA m hm e)
    · exact interval_adjugate_nonpositive L U A hLU hA hp hv

end NLA.IV03

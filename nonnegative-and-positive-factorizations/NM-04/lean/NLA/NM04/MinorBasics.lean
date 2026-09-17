/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The actual increasing enumeration and the empty-minor conventions.
-/
import NLA.NM04.Definitions
import LeanCert.Tactic
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04

-- Match the frozen definitions and Challenge decision instances.
attribute [local instance] Classical.propDecidable

universe u v w

/-- The entries preceding a selected entry are the image of the smaller indices. -/
theorem filter_before_orderEmbOfFin {α : Type u} [LinearOrder α]
    (U : Finset α) (i : Fin U.card) :
    U.filter (fun x => x < U.orderEmbOfFin rfl i) =
      (Finset.Iio i).map (U.orderEmbOfFin rfl).toEmbedding := by
  -- Keep the exact decision family used by the frozen definition of `position`.
  let := Classical.propDecidable
  let e : Fin U.card ↪o α := U.orderEmbOfFin rfl
  have hU : Finset.univ.map e.toEmbedding = U :=
    Finset.map_orderEmbOfFin_univ U rfl
  change U.filter (fun x => x < e i) = (Finset.Iio i).map e.toEmbedding
  calc
    U.filter (fun x => x < e i) =
        (Finset.univ.map e.toEmbedding).filter (fun x => x < e i) := by rw [hU]
    _ = (Finset.Iio i).map e.toEmbedding := by
      rw [Finset.filter_map]
      congr 1
      ext j
      simp

theorem position_sorted_semantics {α : Type u} [LinearOrder α]
    (U : Finset α) (i : Fin U.card) :
    position (U.orderEmbOfFin rfl i) U = i.val + 1 := by
  let := Classical.propDecidable
  unfold position
  rw [filter_before_orderEmbOfFin, Finset.card_map, Fin.card_Iio]

/-- A named cardinality preserves the one-based position convention. -/
theorem position_ordered_card {α : Type u} [LinearOrder α]
    (U : Finset α) {n : ℕ} (h : U.card = n) (i : Fin n) :
    position (U.orderEmbOfFin h i) U = i.val + 1 := by
  subst n
  exact position_sorted_semantics U i

/-- A named cardinality changes only the witnesses of the increasing enumeration.
This elementary transport is also useful for enlarged minors. -/
theorem minor_ordered_det {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) {n : ℕ} (h : I.1.1.card = n) :
    minor T I = (Matrix.of (fun i j : Fin n =>
      T (I.1.1.orderEmbOfFin h i) (I.1.2.orderEmbOfFin (I.property.symm.trans h) j))).det := by
  subst n
  rfl

/-- The determinant convention also applies when both ambient types are empty. -/
theorem minor_empty {α β 𝕜 : Type*} [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) : minor T (emptyIndex α β) = 1 := by
  exact Matrix.det_fin_zero

theorem empty_minor_values {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) :
    minor (tailMatrix A) (emptyIndex (Tail m) (Tail n)) = 1 ∧
    delta A hm hn (emptyIndex (Tail m) (Tail n)) = A (firstIndex hm) (firstIndex hn) ∧
    gamma A hm hn (emptyIndex (Tail m) (Tail n)) = A (firstIndex hm) (firstIndex hn) := by
  refine ⟨minor_empty _, ?_, ?_⟩
  · -- Expose the singleton index type while preserving the determinant instances.
    change (A.submatrix
      (Fin.cons (firstIndex hm) (fun i : Fin 0 =>
        ((∅ : Finset (Tail m)).orderEmbOfFin rfl i).val))
      (Fin.cons (firstIndex hn) (fun j : Fin 0 =>
        ((∅ : Finset (Tail n)).orderEmbOfFin rfl j).val))).det =
      A (firstIndex hm) (firstIndex hn)
    exact Matrix.det_eq_elem_of_subsingleton _ (0 : Fin 1)
  · unfold gamma
    rw [minor_empty, mul_one]

#print axioms minor_ordered_det
#assert_trust kernel minor_ordered_det
#print axioms position_ordered_card
#assert_trust kernel position_ordered_card
#print axioms position_sorted_semantics
#assert_trust kernel position_sorted_semantics
#print axioms empty_minor_values
#assert_trust kernel empty_minor_values

end NLA.NM04

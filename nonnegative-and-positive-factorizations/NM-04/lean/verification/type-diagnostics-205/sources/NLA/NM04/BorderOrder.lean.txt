/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

Explicit finite permutations for ordering an appended row and column.
-/
import NLA.NM04.MinorBasics
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

/-- The distinguished element is moved from its actual increasing position to
the front. The remaining enumeration is increasing and has exactly the old range. -/
theorem insertion_front_order {α : Type u} [LinearOrder α]
    (R : Finset α) (s : α) {k : ℕ}
    (hR : R.card = k) (hU : (insert s R).card = k + 1) :
    ∃ p : Fin (k + 1),
      (Fin.cons s (R.orderEmbOfFin hR) : Fin (k + 1) → α) =
        (insert s R).orderEmbOfFin hU ∘ p.cycleRange.symm ∧
      position s (insert s R) = p.val + 1 := by
  let U := insert s R
  let e := U.orderIsoOfFin hU
  let p : Fin (k + 1) := e.symm ⟨s, Finset.mem_insert_self _ _⟩
  let x : Fin (k + 1) → α := U.orderEmbOfFin hU
  have hxp : x p = s := congrArg Subtype.val (e.apply_symm_apply ⟨s, Finset.mem_insert_self _ _⟩)
  have hremove : p.removeNth x = R.orderEmbOfFin hR := by
    apply Finset.orderEmbOfFin_unique hR
    · intro j
      apply Finset.mem_of_mem_insert_of_ne (U.orderEmbOfFin_mem hU (p.succAbove j))
      intro hj
      have heq : p.succAbove j = p := (U.orderEmbOfFin hU).injective (hj.trans hxp.symm)
      exact Fin.succAbove_ne p j heq
    · exact (U.orderEmbOfFin hU).strictMono.comp (Fin.strictMono_succAbove p)
  refine ⟨p, ?_, ?_⟩
  · calc
      _ = Fin.cons (x p) (p.removeNth x) := congrArg₂ Fin.cons hxp.symm hremove.symm
      _ = _ := Fin.cons_removeNth_eq_comp_cycleRange_symm x p
  · exact (congrArg (fun a => position a U) hxp).symm.trans (position_ordered_card U hU p)

/-- Moving the last row and column to the front uses the same permutation, so
their determinant signs cancel without any parity or nonzero-size assumption. -/
theorem det_snoc_eq_cons {α : Type u} {β : Type v} {𝕜 : Type w} [CommRing 𝕜]
    {k : ℕ} (T : Matrix α β 𝕜) (r : Fin k → α) (c : Fin k → β) (s : α) (t : β) :
    (T.submatrix (Fin.snoc r s) (Fin.snoc c t)).det =
      (T.submatrix (Fin.cons s r) (Fin.cons t c)).det := by
  let A := T.submatrix (Fin.snoc r s) (Fin.snoc c t)
  let e := (Fin.last k).cycleRange.symm
  have hr : (Fin.snoc r s : Fin (k + 1) → α) ∘ e = Fin.cons s r := by
    simpa only [Fin.snoc_last, Fin.removeNth_last, Fin.init_snoc] using
      (Fin.cons_removeNth_eq_comp_cycleRange_symm (Fin.snoc r s) (Fin.last k)).symm
  have hc : (Fin.snoc c t : Fin (k + 1) → β) ∘ e = Fin.cons t c := by
    simpa only [Fin.snoc_last, Fin.removeNth_last, Fin.init_snoc] using
      (Fin.cons_removeNth_eq_comp_cycleRange_symm (Fin.snoc c t) (Fin.last k)).symm
  have hm : A.submatrix e e = T.submatrix (Fin.cons s r) (Fin.cons t c) := by
    ext i j
    exact congrArg₂ (fun a b => T a b) (congrFun hr i) (congrFun hc j)
  calc
    _ = (A.submatrix e e).det := (Matrix.det_submatrix_equiv_self e A).symm
    _ = _ := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜 => M.det) hm

/-- The two explicit insertion permutations give the sum of the source's
one-based positions; the two added units in those positions cancel. -/
theorem det_front_ordered {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (R : Finset α) (C : Finset β) (s : α) (t : β)
    {k : ℕ} (hR : R.card = k) (hC : C.card = k)
    (hU : (insert s R).card = k + 1) (hV : (insert t C).card = k + 1) :
    (T.submatrix (Fin.cons s (R.orderEmbOfFin hR))
      (Fin.cons t (C.orderEmbOfFin hC))).det =
      (-1 : 𝕜) ^ (position s (insert s R) + position t (insert t C)) *
        (T.submatrix ((insert s R).orderEmbOfFin hU)
          ((insert t C).orderEmbOfFin hV)).det := by
  obtain ⟨p, hp, hposp⟩ := insertion_front_order R s hR hU
  obtain ⟨q, hq, hposq⟩ := insertion_front_order C t hC hV
  let A := T.submatrix ((insert s R).orderEmbOfFin hU) ((insert t C).orderEmbOfFin hV)
  have hm : T.submatrix (Fin.cons s (R.orderEmbOfFin hR))
      (Fin.cons t (C.orderEmbOfFin hC)) =
      (A.submatrix p.cycleRange.symm id).submatrix id q.cycleRange.symm := by
    ext i j
    exact congrArg₂ (fun a b => T a b) (congrFun hp i) (congrFun hq j)
  have hsignp : (Equiv.Perm.sign p.cycleRange.symm : 𝕜) = (-1 : 𝕜) ^ p.val := by
    simp [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  have hsignq : (Equiv.Perm.sign q.cycleRange.symm : 𝕜) = (-1 : 𝕜) ^ q.val := by
    simp [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  calc
    _ = ((A.submatrix p.cycleRange.symm id).submatrix id q.cycleRange.symm).det :=
      congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜 => M.det) hm
    _ = (Equiv.Perm.sign q.cycleRange.symm : 𝕜) * (A.submatrix p.cycleRange.symm id).det :=
      Matrix.det_permute' q.cycleRange.symm (A.submatrix p.cycleRange.symm id)
    _ = (Equiv.Perm.sign q.cycleRange.symm : 𝕜) *
        ((Equiv.Perm.sign p.cycleRange.symm : 𝕜) * A.det) :=
      congrArg (fun a : 𝕜 => (Equiv.Perm.sign q.cycleRange.symm : 𝕜) * a)
        (Matrix.det_permute p.cycleRange.symm A)
    _ = _ := by
      rw [hsignp, hsignq, hposp, hposq]
      simp only [pow_add, pow_one]
      ring

#print axioms insertion_front_order
#assert_trust kernel insertion_front_order
#print axioms det_snoc_eq_cons
#assert_trust kernel det_snoc_eq_cons
#print axioms det_front_ordered
#assert_trust kernel det_front_ordered

end
end NLA.NM04

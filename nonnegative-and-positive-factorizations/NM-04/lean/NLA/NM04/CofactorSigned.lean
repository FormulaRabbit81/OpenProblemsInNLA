/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The adjugate sign and the actual increasing enumerations of erased minors.
-/
import NLA.NM04.MinorBasics
import LeanCert.Tactic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

/-- Deleting position `i` leaves the increasing enumeration obtained by skipping
`i`. Uniqueness of increasing enumeration fixes its orientation without a sign. -/
private theorem orderEmbOfFin_erase_apply {α : Type u} [LinearOrder α]
    (U : Finset α) {n : ℕ} (h : U.card = n + 1) (i : Fin (n + 1))
    (hE : (U.erase (U.orderEmbOfFin h i)).card = n) (a : Fin n) :
    (U.erase (U.orderEmbOfFin h i)).orderEmbOfFin hE a =
      U.orderEmbOfFin h (i.succAbove a) := by
  let := Classical.propDecidable
  have hf : (fun b : Fin n => U.orderEmbOfFin h (i.succAbove b)) =
      (U.erase (U.orderEmbOfFin h i)).orderEmbOfFin hE := by
    apply Finset.orderEmbOfFin_unique hE
    · intro b
      apply Finset.mem_erase.mpr
      refine ⟨?_, U.orderEmbOfFin_mem h (i.succAbove b)⟩
      intro heq
      exact Fin.succAbove_ne i b ((U.orderEmbOfFin h).injective heq)
    · exact (U.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove i)
  exact (congrFun hf a).symm

/-- The zero-based matrix cofactor is exactly the minor on the erased sets. -/
private theorem ordered_adjugate_entry {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) {n : ℕ} (h : I.1.1.card = n)
    (i j : Fin n) :
    (Matrix.of (fun a b : Fin n => T (I.1.1.orderEmbOfFin h a)
      (I.1.2.orderEmbOfFin (I.property.symm.trans h) b))).adjugate j i =
      (-1 : 𝕜) ^ (i.val + j.val) *
        minor T (erasedIndex I (I.1.1.orderIsoOfFin h i)
          (I.1.2.orderIsoOfFin (I.property.symm.trans h) j)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let s : I.1.1 := I.1.1.orderIsoOfFin h i
    let t : I.1.2 := I.1.2.orderIsoOfFin (I.property.symm.trans h) j
    let J : MinorIndex α β := erasedIndex I s t
    have hc : I.1.2.card = n + 1 := I.property.symm.trans h
    have hR : (I.1.1.erase (s : α)).card = n := by
      rw [Finset.card_erase_of_mem s.property, h, Nat.succ_sub_one]
    have hC : (I.1.2.erase (t : β)).card = n := by
      rw [Finset.card_erase_of_mem t.property, hc, Nat.add_sub_cancel]
    have hJ : J.1.1.card = n := hR
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 := Matrix.of
      (fun a b => T (I.1.1.orderEmbOfFin h a) (I.1.2.orderEmbOfFin hc b))
    let B : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of
      (fun a b => T ((I.1.1.erase (s : α)).orderEmbOfFin hR a)
        ((I.1.2.erase (t : β)).orderEmbOfFin hC b))
    have hmatrix : A.submatrix i.succAbove j.succAbove = B := by
      ext a b
      exact congrArg₂ (fun x y => T x y)
        (orderEmbOfFin_erase_apply I.1.1 h i hR a).symm
        (orderEmbOfFin_erase_apply I.1.2 hc j hC b).symm
    have hdet : (A.submatrix i.succAbove j.succAbove).det = minor T J := by
      calc
        _ = B.det :=
          congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M.det) hmatrix
        _ = minor T J := (minor_ordered_det T J hJ).symm
    exact (Matrix.adjugate_fin_succ_eq_det_submatrix A j i).trans
      (congrArg (fun x : 𝕜 => (-1 : 𝕜) ^ (i.val + j.val) * x) hdet)

theorem cofactor_signed_minor_formula {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T Z : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I Z =
      ∑ s : I.1.1, ∑ t : I.1.2,
        (-1 : 𝕜) ^ (position (s : α) I.1.1 + position (t : β) I.1.2) *
          Z s t * minor T (erasedIndex I s t) := by
  unfold cofactorForm
  refine Fintype.sum_equiv (I.1.1.orderIsoOfFin rfl).toEquiv _ _ ?_
  intro i
  refine Fintype.sum_equiv (I.1.2.orderIsoOfFin I.property.symm).toEquiv _ _ ?_
  intro j
  have hsign :
      (-1 : 𝕜) ^ (position (I.1.1.orderEmbOfFin rfl i) I.1.1 +
        position (I.1.2.orderEmbOfFin I.property.symm j) I.1.2) =
      (-1 : 𝕜) ^ (i.val + j.val) := by
    rw [position_ordered_card I.1.1 rfl i, position_ordered_card I.1.2 I.property.symm j]
    -- Both source positions are one-based; their extra factors of -1 cancel.
    simp only [pow_add, pow_one]
    ring
  have hadj : (minorMatrix T I).adjugate j i =
      (-1 : 𝕜) ^ (position (I.1.1.orderEmbOfFin rfl i) I.1.1 +
        position (I.1.2.orderEmbOfFin I.property.symm j) I.1.2) *
        minor T (erasedIndex I (I.1.1.orderIsoOfFin rfl i)
          (I.1.2.orderIsoOfFin I.property.symm j)) :=
    (ordered_adjugate_entry T I rfl i j).trans
      (congrArg (fun x : 𝕜 => x *
        minor T (erasedIndex I (I.1.1.orderIsoOfFin rfl i)
          (I.1.2.orderIsoOfFin I.property.symm j))) hsign.symm)
  calc
    _ = ((-1 : 𝕜) ^ (position (I.1.1.orderEmbOfFin rfl i) I.1.1 +
          position (I.1.2.orderEmbOfFin I.property.symm j) I.1.2) *
          minor T (erasedIndex I (I.1.1.orderIsoOfFin rfl i)
            (I.1.2.orderIsoOfFin I.property.symm j))) *
          Z (I.1.1.orderEmbOfFin rfl i) (I.1.2.orderEmbOfFin I.property.symm j) :=
      congrArg (fun x : 𝕜 => x *
        Z (I.1.1.orderEmbOfFin rfl i) (I.1.2.orderEmbOfFin I.property.symm j)) hadj
    _ = _ := mul_right_comm _ _ _

#print axioms cofactor_signed_minor_formula
#assert_trust kernel cofactor_signed_minor_formula

end
end NLA.NM04

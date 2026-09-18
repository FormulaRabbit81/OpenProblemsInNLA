/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The actual appended border, its repeated-row/column zeros, and its ordered sign.
-/
import NLA.NM04.BorderOrder
import NLA.NM04.MinorTranspose
import NLA.NM04.RaisingIndices
import NLA.NM04.RankOneBordered
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

def borderedMinor {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] (T : Matrix α β 𝕜) (I : MinorIndex α β) (s : α) (t : β) :
    Matrix (Fin (I.1.1.card + 1)) (Fin (I.1.1.card + 1)) 𝕜 :=
  T.submatrix (Fin.snoc (I.1.1.orderEmbOfFin rfl) s)
    (Fin.snoc (I.1.2.orderEmbOfFin I.property.symm) t)

theorem borderedMinor_eq_matrix {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] (T : Matrix α β 𝕜) (I : MinorIndex α β) (s : α) (t : β) :
    borderedMinor T I s t = borderedMatrix (minorMatrix T I)
      (fun j => T s (I.1.2.orderEmbOfFin I.property.symm j))
      (fun i => T (I.1.1.orderEmbOfFin rfl i) t) (T s t) := by
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp only [borderedMinor, Matrix.submatrix_apply, borderedMatrix,
      Fin.snoc_last, Fin.snoc_castSucc, minorMatrix]

theorem borderedMinor_det_of_row_mem {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) (s : α) (t : β) (hs : s ∈ I.1.1) :
    (borderedMinor T I s t).det = 0 := by
  let i : Fin I.1.1.card := (I.1.1.orderIsoOfFin rfl).symm ⟨s, hs⟩
  have hi : I.1.1.orderEmbOfFin rfl i = s :=
    congrArg Subtype.val ((I.1.1.orderIsoOfFin rfl).apply_symm_apply ⟨s, hs⟩)
  apply Matrix.det_zero_of_row_eq (Fin.castSucc_ne_last i)
  funext j
  simp only [borderedMinor, Matrix.submatrix_apply, Fin.snoc_castSucc, Fin.snoc_last, hi]

theorem borderedMinor_det_of_column_mem {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) (s : α) (t : β) (ht : t ∈ I.1.2) :
    (borderedMinor T I s t).det = 0 := by
  let j : Fin I.1.1.card := (I.1.2.orderIsoOfFin I.property.symm).symm ⟨t, ht⟩
  have hj : I.1.2.orderEmbOfFin I.property.symm j = t :=
    congrArg Subtype.val ((I.1.2.orderIsoOfFin I.property.symm).apply_symm_apply ⟨t, ht⟩)
  apply Matrix.det_zero_of_column_eq (Fin.castSucc_ne_last j)
  intro i
  simp only [borderedMinor, Matrix.submatrix_apply, Fin.snoc_castSucc, Fin.snoc_last, hj]

/-- The explicit permutations in `BorderOrder` produce precisely the frozen
raising sign. Both order-zero and singular leading blocks are included. -/
theorem borderedMinor_det_of_not_mem {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (s : {s : α // s ∉ I.1.1}) (t : {t : β // t ∉ I.1.2}) :
    (borderedMinor T I s t).det =
      (-1 : 𝕜) ^ (position (s : α) (raisingIndex I s t).1.1 +
        position (t : β) (raisingIndex I s t).1.2) * minor T (raisingIndex I s t) := by
  let k := I.1.1.card
  let J := raisingIndex I s t
  have hR : (insert (s : α) I.1.1).card = k + 1 := Finset.card_insert_of_notMem s.property
  have hC : (insert (t : β) I.1.2).card = k + 1 :=
    (Finset.card_insert_of_notMem t.property).trans (congrArg (fun n : ℕ => n + 1) I.property.symm)
  calc
    _ = (T.submatrix (Fin.cons s (I.1.1.orderEmbOfFin rfl))
        (Fin.cons t (I.1.2.orderEmbOfFin I.property.symm))).det :=
      det_snoc_eq_cons T (I.1.1.orderEmbOfFin rfl) (I.1.2.orderEmbOfFin I.property.symm) s t
    _ = (-1 : 𝕜) ^ (position (s : α) J.1.1 + position (t : β) J.1.2) *
        (T.submatrix (J.1.1.orderEmbOfFin hR) (J.1.2.orderEmbOfFin hC)).det :=
      det_front_ordered T I.1.1 I.1.2 s t rfl I.property.symm hR hC
    _ = _ := congrArg
      (fun z : 𝕜 => (-1 : 𝕜) ^ (position (s : α) J.1.1 + position (t : β) J.1.2) * z)
      (minor_ordered_det T J hR).symm

/-- C22 applies to the literal border of every ambient row/column pair. -/
theorem cofactorForm_border_entry {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) (s : α) (t : β) :
    cofactorForm T I (Matrix.vecMulVec (fun r => T r t) (fun c => T s c)) =
      T s t * minor T I - (borderedMinor T I s t).det := by
  let A := minorMatrix T I
  let a : Fin I.1.1.card → 𝕜 := fun j => T s (I.1.2.orderEmbOfFin I.property.symm j)
  let b : Fin I.1.1.card → 𝕜 := fun i => T (I.1.1.orderEmbOfFin rfl i) t
  have hsum : cofactorForm T I (Matrix.vecMulVec (fun r => T r t) (fun c => T s c)) =
      ∑ j : Fin I.1.1.card, a j * (A.adjugate.mulVec b) j := by
    change (∑ i : Fin I.1.1.card, ∑ j : Fin I.1.1.card,
        A.adjugate j i * (b i * a j)) =
      ∑ j : Fin I.1.1.card, a j * ∑ i : Fin I.1.1.card, A.adjugate j i * b i
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ = ∑ j : Fin I.1.1.card, a j * (A.adjugate.mulVec b) j := hsum
    _ = T s t * A.det - (borderedMatrix A a b (T s t)).det :=
      universal_bordered_determinant A a b (T s t)
    _ = _ := congrArg (fun M : Matrix (Fin (I.1.1.card + 1)) (Fin (I.1.1.card + 1)) 𝕜 =>
      T s t * A.det - M.det) (borderedMinor_eq_matrix T I s t).symm

#print axioms borderedMinor_eq_matrix
#assert_trust kernel borderedMinor_eq_matrix
#print axioms borderedMinor_det_of_row_mem
#assert_trust kernel borderedMinor_det_of_row_mem
#print axioms borderedMinor_det_of_column_mem
#assert_trust kernel borderedMinor_det_of_column_mem
#print axioms borderedMinor_det_of_not_mem
#assert_trust kernel borderedMinor_det_of_not_mem
#print axioms cofactorForm_border_entry
#assert_trust kernel cofactorForm_border_entry

end
end NLA.NM04

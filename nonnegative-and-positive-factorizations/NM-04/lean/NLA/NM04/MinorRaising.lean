/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The exact raising identity, from the universal border and all ambient row/column pairs.
-/
import NLA.NM04.BorderedMinors
import NLA.NM04.MinorLinearity
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

/-- Expand the row-sum/column-sum direction into its actual ambient pairs, then
use the already proved finite-sum linearity of the cofactor form. -/
theorem cofactorForm_row_column_sum {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I (Matrix.vecMulVec (fun r => ∑ t, T r t) (fun c => ∑ s, T s c)) =
      ∑ s : α, ∑ t : β,
        cofactorForm T I (Matrix.vecMulVec (fun r => T r t) (fun c => T s c)) := by
  have hZ : Matrix.vecMulVec (fun r => ∑ t, T r t) (fun c => ∑ s, T s c) =
      ∑ s : α, ∑ t : β, Matrix.vecMulVec (fun r => T r t) (fun c => T s c) := by
    ext r c
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = cofactorForm T I
        (∑ s : α, ∑ t : β, Matrix.vecMulVec (fun r => T r t) (fun c => T s c)) :=
      congrArg (cofactorForm T I) hZ
    _ = ∑ s : α, cofactorForm T I
        (∑ t : β, Matrix.vecMulVec (fun r => T r t) (fun c => T s c)) :=
      cofactorForm_sum T I Finset.univ
        (fun s : α => ∑ t : β, Matrix.vecMulVec (fun r => T r t) (fun c => T s c))
    _ = _ := Finset.sum_congr rfl (fun s _ =>
      cofactorForm_sum T I Finset.univ
        (fun t : β => Matrix.vecMulVec (fun r => T r t) (fun c => T s c)))

/-- The border vanishes on every selected ambient row or column. The remaining
pairs are exactly, and injectively, the terms in the frozen raising operator. -/
theorem borderedMinor_sum {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    (∑ s : α, ∑ t : β, (borderedMinor T I s t).det) = raising (minor T) I := by
  symm
  calc
    _ = ∑ s : {s : α // s ∉ I.1.1}, ∑ t : {t : β // t ∉ I.1.2},
        (-1 : 𝕜) ^ (position (s : α) (raisingIndex I s t).1.1 +
          position (t : β) (raisingIndex I s t).1.2) * minor T (raisingIndex I s t) :=
      raising_eq_index_sum (minor T) I
    _ = ∑ s : {s : α // s ∉ I.1.1}, ∑ t : {t : β // t ∉ I.1.2},
        (borderedMinor T I s t).det := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      exact (borderedMinor_det_of_not_mem T I s t).symm
    _ = ∑ p : {s : α // s ∉ I.1.1} × {t : β // t ∉ I.1.2},
        (borderedMinor T I p.1 p.2).det :=
      (Fintype.sum_prod_type (fun p : {s : α // s ∉ I.1.1} × {t : β // t ∉ I.1.2} =>
        (borderedMinor T I p.1 p.2).det)).symm
    _ = ∑ p : α × β, (borderedMinor T I p.1 p.2).det := by
      apply Fintype.sum_of_injective
        (fun p : {s : α // s ∉ I.1.1} × {t : β // t ∉ I.1.2} => ((p.1 : α), (p.2 : β)))
        (fun p q h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
          (Subtype.ext (congrArg Prod.snd h)))
      · intro p hp
        by_cases hs : p.1 ∈ I.1.1
        · exact borderedMinor_det_of_row_mem T I p.1 p.2 hs
        · by_cases ht : p.2 ∈ I.1.2
          · exact borderedMinor_det_of_column_mem T I p.1 p.2 ht
          · exact False.elim (hp ⟨(⟨p.1, hs⟩, ⟨p.2, ht⟩), rfl⟩)
      · intro p
        rfl
    _ = _ := Fintype.sum_prod_type (fun p : α × β => (borderedMinor T I p.1 p.2).det)

theorem minor_raising_identity {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I
        (Matrix.vecMulVec (fun i => ∑ j, T i j) (fun j => ∑ i, T i j)) =
      (∑ i, ∑ j, T i j) * minor T I - raising (minor T) I := by
  calc
    _ = ∑ s : α, ∑ t : β,
        cofactorForm T I (Matrix.vecMulVec (fun r => T r t) (fun c => T s c)) :=
      cofactorForm_row_column_sum T I
    _ = ∑ s : α, ∑ t : β, (T s t * minor T I - (borderedMinor T I s t).det) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      exact cofactorForm_border_entry T I s t
    _ = (∑ s : α, ∑ t : β, T s t) * minor T I -
        ∑ s : α, ∑ t : β, (borderedMinor T I s t).det := by
      simp only [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := congrArg (fun z : 𝕜 => (∑ s : α, ∑ t : β, T s t) * minor T I - z)
      (borderedMinor_sum T I)

#print axioms cofactorForm_row_column_sum
#assert_trust kernel cofactorForm_row_column_sum
#print axioms borderedMinor_sum
#assert_trust kernel borderedMinor_sum
#print axioms minor_raising_identity
#assert_trust kernel minor_raising_identity

end
end NLA.NM04

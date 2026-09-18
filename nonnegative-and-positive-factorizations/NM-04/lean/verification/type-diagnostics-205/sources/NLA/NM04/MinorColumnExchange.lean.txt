/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The exact signed column-exchange identity, including empty and singular minors.
-/
import NLA.NM04.MinorColumnForms
import NLA.NM04.ColumnExchangeIndices
import Mathlib.Tactic.Ring
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

/-- Compare two signed Laplace expansions on the same erased column set.
The two factors from the added column's position cancel exactly. -/
theorem minorColumnForm_exchange {α : Type u} {β : Type v} {𝕜 : Type w}
    [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β)
    (s : I.1.2) (t : {t : β // t ∉ I.1.2}) :
    minorColumnForm T I s (fun r => T r t) =
      (-1 : 𝕜) ^ (position (s : β) I.1.2 +
        position (t : β) (columnExchangeIndex I s t).1.2) *
          minor T (columnExchangeIndex I s t) := by
  let J := columnExchangeIndex I s t
  let tJ : J.1.2 := ⟨t.val, Finset.mem_insert_self _ _⟩
  have ht : t.val ∉ I.1.2.erase s.val := fun h => t.property (Finset.mem_of_mem_erase h)
  have herase (r : I.1.1) : erasedIndex J r tJ = erasedIndex I r s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Finset.erase_insert ht
  calc
    _ = ∑ r : I.1.1,
        (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (s : β) I.1.2) *
          T r t * minor T (erasedIndex I r s) :=
      minorColumnForm_signed T I s (fun r => T r t)
    _ = (-1 : 𝕜) ^ (position (s : β) I.1.2 + position (tJ : β) J.1.2) *
        (∑ r : J.1.1,
          (-1 : 𝕜) ^ (position (r : α) J.1.1 + position (tJ : β) J.1.2) *
            T r tJ * minor T (erasedIndex J r tJ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      have hm : minor T (erasedIndex J r tJ) = minor T (erasedIndex I r s) :=
        congrArg (minor T) (herase r)
      have hsign :
          (-1 : 𝕜) ^ (position (s : β) I.1.2 + position (tJ : β) J.1.2) *
            (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (tJ : β) J.1.2) =
          (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (s : β) I.1.2) := by
        simp only [pow_add]
        rcases neg_one_pow_eq_or 𝕜 (position (tJ : β) J.1.2) with h | h <;> rw [h] <;> ring
      change (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (s : β) I.1.2) *
          T r t * minor T (erasedIndex I r s) =
        (-1 : 𝕜) ^ (position (s : β) I.1.2 + position (tJ : β) J.1.2) *
          ((-1 : 𝕜) ^ (position (r : α) I.1.1 + position (tJ : β) J.1.2) *
            T r t * minor T (erasedIndex J r tJ))
      rw [hm]
      calc
        _ = ((-1 : 𝕜) ^ (position (s : β) I.1.2 + position (tJ : β) J.1.2) *
            (-1 : 𝕜) ^ (position (r : α) I.1.1 + position (tJ : β) J.1.2)) *
              T r t * minor T (erasedIndex I r s) :=
          congrArg (fun a : 𝕜 => a * T r t * minor T (erasedIndex I r s)) hsign.symm
        _ = _ := by ring
    _ = _ := congrArg
      (fun a : 𝕜 => (-1 : 𝕜) ^ (position (s : β) I.1.2 + position (tJ : β) J.1.2) * a)
      (minor_laplace_column T J tJ).symm

/-- Expand the row-sum direction as all individual column replacements. -/
theorem cofactorForm_column_sum {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I (Matrix.vecMulVec (fun r => ∑ t, T r t) (fun _ => 1)) =
      ∑ s : I.1.2, ∑ t : β, minorColumnForm T I s (fun r => T r t) := by
  let A := minorMatrix T I
  let e := I.1.2.orderIsoOfFin I.property.symm
  calc
    _ = ∑ j : Fin I.1.1.card, ∑ t : β, ∑ i : Fin I.1.1.card,
        A.adjugate j i * T (I.1.1.orderEmbOfFin rfl i) t := by
      change (∑ i : Fin I.1.1.card, ∑ j : Fin I.1.1.card,
          A.adjugate j i * ((∑ t : β, T (I.1.1.orderEmbOfFin rfl i) t) * 1)) = _
      simp only [mul_one, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by
      refine Fintype.sum_equiv e.toEquiv _ _ ?_
      intro j
      apply Finset.sum_congr rfl
      intro t _
      calc
        _ = ∑ i : Fin I.1.1.card, A.adjugate (e.symm (e j)) i *
            T (I.1.1.orderEmbOfFin rfl i) t :=
          congrArg (fun l : Fin I.1.1.card => ∑ i : Fin I.1.1.card,
            A.adjugate l i * T (I.1.1.orderEmbOfFin rfl i) t) (e.symm_apply_apply j).symm
        _ = _ := (minorColumnForm_adjugate T I (e j) (fun r => T r t)).symm

theorem minor_column_exchange_identity {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I (Matrix.vecMulVec (fun i => ∑ j, T i j) (fun _ => 1)) =
      (I.1.1.card : 𝕜) * minor T I + columnExchange (minor T) I := by
  have hselected (s : I.1.2) :
      (∑ d : I.1.2, minorColumnForm T I s (fun r => T r d)) = minor T I := by
    calc
      _ = ∑ d : I.1.2, if d = s then minor T I else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        exact minorColumnForm_selected T I s d
      _ = _ := by simp
  -- The generic predicate partition and the finite-set subtype supply equal
  -- finite enumerations through different instances. Transport the actual univ.
  have huniv : @Finset.univ I.1.2 (Subtype.fintype (fun t : β => t ∈ I.1.2)) =
      @Finset.univ I.1.2 (Finset.Subtype.fintype I.1.2) :=
    congrArg (fun d : Fintype I.1.2 => @Finset.univ I.1.2 d) (Subsingleton.elim _ _)
  calc
    _ = ∑ s : I.1.2, ∑ t : β, minorColumnForm T I s (fun r => T r t) :=
      cofactorForm_column_sum T I
    _ = ∑ s : I.1.2, (minor T I + ∑ t : {t : β // t ∉ I.1.2},
        (-1 : 𝕜) ^ (position (s : β) I.1.2 +
          position (t : β) (columnExchangeIndex I s t).1.2) *
            minor T (columnExchangeIndex I s t)) := by
      apply Finset.sum_congr rfl
      intro s _
      calc
        _ = (∑ d : I.1.2, minorColumnForm T I s (fun r => T r d)) +
            ∑ t : {t : β // t ∉ I.1.2}, minorColumnForm T I s (fun r => T r t) := by
          simpa only [huniv] using
            (Fintype.sum_subtype_add_sum_subtype (fun t : β => t ∈ I.1.2)
              (fun t => minorColumnForm T I s (fun r => T r t))).symm
        _ = _ := congrArg₂ (· + ·) (hselected s) (Finset.sum_congr rfl
          (fun t _ => minorColumnForm_exchange T I s t))
    _ = (I.1.2.card : 𝕜) * minor T I + columnExchange (minor T) I := by
      rw [Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      · exact (columnExchange_eq_index_sum (minor T) I).symm
    _ = _ := congrArg (fun n : ℕ => (n : 𝕜) * minor T I + columnExchange (minor T) I)
      I.property.symm

#print axioms minorColumnForm_exchange
#assert_trust kernel minorColumnForm_exchange
#print axioms cofactorForm_column_sum
#assert_trust kernel cofactorForm_column_sum
#print axioms minor_column_exchange_identity
#assert_trust kernel minor_column_exchange_identity

end
end NLA.NM04

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The selected-pair erasure sum is the literal lowering operator on all minor indices.
-/
import NLA.NM04.CofactorSigned
import NLA.NM04.TransitionSupport
import LeanCert.Tactic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v w

/-- Erasing a selected pair has exactly the four literal lowering differences. -/
private theorem erasedIndex_loweringSupport {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β) (s : I.1.1) (t : I.1.2) :
    LoweringSupport I (erasedIndex I s t) s t := by
  change I.1.1 \ I.1.1.erase s = {s.val} ∧ I.1.1.erase s \ I.1.1 = ∅ ∧
    I.1.2 \ I.1.2.erase t = {t.val} ∧ I.1.2.erase t \ I.1.2 = ∅
  exact ⟨Finset.sdiff_erase_self s.property,
    Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _),
    Finset.sdiff_erase_self t.property,
    Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _)⟩

/-- Conversely the singleton/empty differences determine the erased sets. -/
private theorem loweringSupport_erasedIndex {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] {I J : MinorIndex α β} {s : α} {t : β}
    (h : LoweringSupport I J s t) :
    ∃ s' : I.1.1, ∃ t' : I.1.2, erasedIndex I s' t' = J := by
  have hs : s ∈ I.1.1 :=
    (Finset.mem_sdiff.mp (h.1.symm ▸ Finset.mem_singleton_self s)).1
  have ht : t ∈ I.1.2 :=
    (Finset.mem_sdiff.mp (h.2.2.1.symm ▸ Finset.mem_singleton_self t)).1
  refine ⟨⟨s, hs⟩, ⟨t, ht⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change I.1.1.erase s = J.1.1
    calc
      _ = I.1.1 \ {s} := Finset.erase_eq _ _
      _ = I.1.1 \ (I.1.1 \ J.1.1) := congrArg (fun U => I.1.1 \ U) h.1.symm
      _ = J.1.1 := Finset.sdiff_sdiff_eq_self
        (Finset.sdiff_eq_empty_iff_subset.mp h.2.1)
  · change I.1.2.erase t = J.1.2
    calc
      _ = I.1.2 \ {t} := Finset.erase_eq _ _
      _ = I.1.2 \ (I.1.2 \ J.1.2) := congrArg (fun U => I.1.2 \ U) h.2.2.1.symm
      _ = J.1.2 := Finset.sdiff_sdiff_eq_self
        (Finset.sdiff_eq_empty_iff_subset.mp h.2.2.2)

/-- Different selected pairs cannot produce the same erased minor index. -/
private theorem erasedIndex_pair_injective {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β] (I : MinorIndex α β) :
    Function.Injective (fun p : I.1.1 × I.1.2 => erasedIndex I p.1 p.2) := by
  intro p q hpq
  change erasedIndex I p.1 p.2 = erasedIndex I q.1 q.2 at hpq
  have hp := erasedIndex_loweringSupport I p.1 p.2
  have hq : LoweringSupport I (erasedIndex I p.1 p.2) q.1 q.2 := by
    rw [hpq]
    exact erasedIndex_loweringSupport I q.1 q.2
  have h := (hp.iff_eq q.1 q.2).mp hq
  exact Prod.ext (Subtype.ext h.1.symm) (Subtype.ext h.2.symm)

/-- Reindexing is valid for every function of minors: unsupported indices
contribute zero, and every supported index arises from exactly one erased pair. -/
private theorem lowering_eq_erased_sum {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (f : MinorIndex α β → 𝕜) (I : MinorIndex α β) :
    lowering f I = ∑ s : I.1.1, ∑ t : I.1.2,
      (-1 : 𝕜) ^ (position (s : α) I.1.1 + position (t : β) I.1.2) *
        f (erasedIndex I s t) := by
  symm
  calc
    _ = ∑ p : I.1.1 × I.1.2,
        (-1 : 𝕜) ^ (position (p.1 : α) I.1.1 + position (p.2 : β) I.1.2) *
          f (erasedIndex I p.1 p.2) := (Fintype.sum_prod_type _).symm
    _ = lowering f I := by
      unfold lowering
      apply Fintype.sum_of_injective
        (fun p : I.1.1 × I.1.2 => erasedIndex I p.1 p.2) (erasedIndex_pair_injective I)
      · intro J hJ
        have hzero : loweringCoefficient I J = 0 := loweringCoefficient_zero (by
          intro s t hst
          obtain ⟨s', t', he⟩ := loweringSupport_erasedIndex hst
          exact hJ ⟨(s', t'), he⟩)
        simp only [hzero, Int.cast_zero, zero_mul]
      · intro p
        rw [loweringCoefficient_of_support (erasedIndex_loweringSupport I p.1 p.2)]
        simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

theorem minor_lowering_identity {α : Type u} {β : Type v} {𝕜 : Type w}
    [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] [CommRing 𝕜]
    (T : Matrix α β 𝕜) (I : MinorIndex α β) :
    cofactorForm T I (fun _ _ => 1) = lowering (minor T) I := by
  calc
    _ = ∑ s : I.1.1, ∑ t : I.1.2,
        (-1 : 𝕜) ^ (position (s : α) I.1.1 + position (t : β) I.1.2) *
          1 * minor T (erasedIndex I s t) :=
      cofactor_signed_minor_formula T (fun _ _ => 1) I
    _ = ∑ s : I.1.1, ∑ t : I.1.2,
        (-1 : 𝕜) ^ (position (s : α) I.1.1 + position (t : β) I.1.2) *
          minor T (erasedIndex I s t) := by simp only [mul_one]
    _ = lowering (minor T) I := (lowering_eq_erased_sum (minor T) I).symm

#print axioms minor_lowering_identity
#assert_trust kernel minor_lowering_identity

end
end NLA.NM04

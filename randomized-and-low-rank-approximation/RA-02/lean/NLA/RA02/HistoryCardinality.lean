/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Counts the actual unused original labels. No retained binary path restriction
or terminal one-label condition is assumed in the counting invariant.
-/
import NLA.RA02.HistoryLabels
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma remaining_label_cardinality (r : ℕ) (w : List (Fin (r + 1))) (hw : w.Nodup) :
    (remainingOrdinary r w).card + w.length + (if lastRemaining r w then 1 else 0) = r + 1 := by
  revert hw
  induction w using List.reverseRecOn with
  | nil =>
      intro _
      simp
  | append_singleton w j ih =>
      intro hw
      have hw' : w.Nodup := (List.nodup_append.mp hw).1
      have hj : j ∉ w := by
        intro hjw
        exact (List.nodup_append.mp hw).2.2 j hjw j (by simp) rfl
      have hcard := ih hw'
      revert hj
      refine Fin.lastCases ?_ (fun i => ?_) j
      · intro hlast
        rw [lastRemaining_of_not_mem r w hlast] at hcard
        rw [remainingOrdinary_append_last, lastRemaining_append_last]
        simp only [List.length_append, List.length_singleton,
          Bool.false_eq_true, ↓reduceIte] at *
        omega
      · intro hi
        have hiU : i ∈ remainingOrdinary r w := (mem_remainingOrdinary r w i).2 hi
        have herase := Finset.card_erase_add_one hiU
        rw [remainingOrdinary_append_ordinary, lastRemaining_append_ordinary]
        simp only [List.length_append, List.length_singleton]
        omega

lemma remaining_nonempty_or_last (r : ℕ) (w : List (Fin (r + 1)))
    (hw : w.Nodup) (hlen : w.length ≤ r) :
    lastRemaining r w = true ∨ (remainingOrdinary r w).Nonempty := by
  have hcard := remaining_label_cardinality r w hw
  cases hb : lastRemaining r w
  · right
    rw [hb] at hcard
    simp only [Bool.false_eq_true, ↓reduceIte] at hcard
    apply Finset.card_pos.mp
    omega
  · exact Or.inl rfl

lemma terminal_remaining_cardinality (r : ℕ) (w : List (Fin (r + 1)))
    (hw : w.Nodup) (hlen : w.length = r) :
    (remainingOrdinary r w).card + (if lastRemaining r w then 1 else 0) = 1 := by
  have hcard := remaining_label_cardinality r w hw
  rw [hlen] at hcard
  omega

#print axioms remaining_label_cardinality
#assert_trust kernel remaining_label_cardinality

end
end NLA.RA02

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Every distinct original-label history has the displayed full residual state.
The argument is chronological and does not assume independent pivot choices.
-/
import NLA.RA02.StateUpdates
import NLA.RA02.HistoryLabels
import NLA.RA02.PathSemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma pathResidual_distinct_state (r : ℕ) (w : List (Fin (r + 1))) (hw : w.Nodup) :
    pathResidual (arrowhead r) w =
      arrowheadState r (remainingOrdinary r w) (lastRemaining r w) := by
  revert hw
  induction w using List.reverseRecOn with
  | nil =>
      intro _
      simp [pathResidual, arrowhead]
  | append_singleton w j ih =>
      intro hw
      have hw' : w.Nodup := (List.nodup_append.mp hw).1
      have hj : j ∉ w := by
        intro hjw
        exact (List.nodup_append.mp hw).2.2 j hjw j (by simp) rfl
      rw [pathResidual_append]
      change choleskyStep (pathResidual (arrowhead r) w) j =
        arrowheadState r (remainingOrdinary r (w ++ [j])) (lastRemaining r (w ++ [j]))
      rw [ih hw']
      revert hj
      refine Fin.lastCases ?_ (fun i => ?_) j
      · intro hlast
        rw [lastRemaining_of_not_mem r w hlast, remainingOrdinary_append_last,
          lastRemaining_append_last, state_true_last_pivot]
      · intro hi
        have hiU : i ∈ remainingOrdinary r w := (mem_remainingOrdinary r w i).2 hi
        rw [remainingOrdinary_append_ordinary, lastRemaining_append_ordinary]
        cases lastRemaining r w
        · exact state_false_ordinary_pivot r (remainingOrdinary r w) i hiU
        · exact state_true_ordinary_pivot r (remainingOrdinary r w) i hiU

theorem distinct_history_state (r : ℕ) (hr : 1 ≤ r) (w : List (Fin (r + 1)))
    (hw : w.Nodup) (hlen : w.length ≤ r + 1) :
    pathResidual (arrowhead r) w =
      arrowheadState r (remainingOrdinary r w) (lastRemaining r w) := by
  exact pathResidual_distinct_state r w hw

#print axioms pathResidual_distinct_state
#assert_trust kernel pathResidual_distinct_state
#print axioms distinct_history_state
#assert_trust kernel distinct_history_state

end
end NLA.RA02

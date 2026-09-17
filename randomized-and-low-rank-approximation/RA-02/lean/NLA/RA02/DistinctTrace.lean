/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Every required distinct-history prefix has an actual positive residual trace.
This proves the normalization premise used by the conditional-law bridge.
-/
import NLA.RA02.HistoryCardinality
import NLA.RA02.DistinctHistory

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma distinct_prefix_trace_pos (r : ℕ) (hr : 1 ≤ r) (w : List (Fin (r + 1)))
    (hw : w.Nodup) (hlen : w.length ≤ r) :
    0 < realTrace (pathResidual (arrowhead r) w) := by
  rw [pathResidual_distinct_state r w hw]
  have hPSD := (residual_state_positivity r hr (remainingOrdinary r w)).2.1
    (lastRemaining r w)
  apply realTrace_pos hPSD
  rcases remaining_nonempty_or_last r w hw hlen with hb | ⟨i, hi⟩
  · rw [hb]
    intro hz
    have hentry := congrArg (fun A : Square (r + 1) => (A (Fin.last r) (Fin.last r)).re) hz
    have hc : cornerValue r (remainingOrdinary r w) = 0 := by simpa using hentry
    exact (cornerValue_pos r (remainingOrdinary r w)).ne' hc
  · intro hz
    apply state_active_pivot_ne_zero r (remainingOrdinary r w) (lastRemaining r w) i hi
    exact congrArg (fun A : Square (r + 1) => A i.castSucc i.castSucc) hz

lemma distinct_history_prefix_traces (r : ℕ) (hr : 1 ≤ r) (w : List (Fin (r + 1)))
    (hw : w.Nodup) (hlen : w.length = r) :
    ∀ s : Fin w.length, 0 < realTrace (pathResidual (arrowhead r) (w.take s.val)) := by
  intro s
  apply distinct_prefix_trace_pos r hr (w.take s.val)
  · exact (List.take_sublist s.val w).nodup hw
  · have htake := List.length_take_le s.val w
    have hs := s.isLt
    omega

#print axioms distinct_prefix_trace_pos
#assert_trust kernel distinct_prefix_trace_pos
#print axioms distinct_history_prefix_traces
#assert_trust kernel distinct_history_prefix_traces

end
end NLA.RA02

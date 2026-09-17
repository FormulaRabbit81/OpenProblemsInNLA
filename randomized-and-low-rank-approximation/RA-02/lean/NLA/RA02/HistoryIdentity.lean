/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The exact frozen distinct-history identity, with every chronological trace
normalization retained. No retained-history counting claim is made here.
-/
import NLA.RA02.StateTrace
import NLA.RA02.DistinctTrace

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

theorem distinct_history_identity (r : ℕ) (hr : 1 ≤ r) (w : List (Fin (r + 1)))
    (hw : w.Nodup) (hlen : w.length = r) :
    pivotProduct (arrowhead r) w * realTrace (pathResidual (arrowhead r) w) = commonNumerator r ∧
    pathContribution (arrowhead r) w = commonNumerator r / prefixTraceProduct (arrowhead r) w := by
  have hcard := terminal_remaining_cardinality r w hw hlen
  have hfirst : pivotProduct (arrowhead r) w *
      realTrace (pathResidual (arrowhead r) w) = commonNumerator r := by
    rw [pathResidual_distinct_state r w hw,
      state_trace_eq_potential_when_one r (remainingOrdinary r w) (lastRemaining r w) hcard]
    exact pivotProduct_statePotential r w hw
  refine ⟨hfirst, ?_⟩
  have htrace := distinct_history_prefix_traces r hr w hw hlen
  rw [pathContribution,
    pathWeight_eq_pivotProduct_div (arrowhead r) w (fun s => (htrace s).ne'),
    div_mul_eq_mul_div, hfirst]

#print axioms distinct_history_identity
#assert_trust kernel distinct_history_identity

end
end NLA.RA02

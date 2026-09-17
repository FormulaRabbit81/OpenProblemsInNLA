/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain the original
question; Matthew J. Colbrook retains the complete coefficient-identity proof.

The concrete sinkhorn definition chooses the uniquely scaled positive
matrix. Actual existence excludes its zero fallback; actual uniqueness
identifies every matrix meeting the canonical scaling and margin conditions.
-/
import NLA.NM04.ScalingExistence
import NLA.NM04.ScalingUniqueness

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04

theorem sinkhorn_semantics {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) :
    ScaledBalanced A (sinkhorn A) ∧ Positive (sinkhorn A) ∧
      ∀ S : Rect m n, ScaledBalanced A S → S = sinkhorn A := by
  classical
  have hex : ∃ S : Rect m n, ScaledBalanced A S :=
    positive_balanced_scaling_exists hm hn A hA
  have hchosen : ScaledBalanced A (sinkhorn A) := by
    simpa only [sinkhorn, dif_pos hex] using Classical.choose_spec hex
  refine ⟨hchosen, scaledBalanced_positive A (sinkhorn A) hA hchosen, ?_⟩
  intro S hS
  exact positive_balanced_scaling_unique hm hn A hA S (sinkhorn A) hS hchosen

#print axioms sinkhorn_semantics
#assert_trust kernel sinkhorn_semantics

end NLA.NM04

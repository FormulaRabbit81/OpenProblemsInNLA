/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.

The original Gram kernel intersects the genuine compact Euclidean sphere.
Continuity of the actual inner products preserves compactness under gradient.
These topology lemmas make no convexity or minimax assumption.
-/
import NLA.IE02.NormAttainment
import NLA.IE02.MaximalSpace

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem gradient_continuous {n k : ℕ} (T : Square n) (R : Fin k → Square n) :
    Continuous (gradient T R) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin k => ℂ)).comp
  apply continuous_pi
  intro j
  exact (euclideanCLM T).continuous.inner (euclideanCLM (R j)).continuous

theorem unitMaximal_nonempty_compact {n : ℕ} (hn : 1 ≤ n) (T : Square n) :
    (unitMaximal T).Nonempty ∧ IsCompact (unitMaximal T) := by
  have hmax := maximal_space_norm T
  constructor
  · obtain ⟨x, hx, hTx⟩ := (euclidean_norm_attainment hn T).2.2.2
    refine ⟨x, (hmax.2 x).mpr ?_, hx⟩
    have hnx : ‖x‖ = 1 := hx
    rw [hnx, mul_one]
    exact hTx
  · have hsphere : unitSphere n = Metric.sphere (0 : H n) 1 := by
      ext x
      simp only [unitSphere, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
    have hc : IsCompact (unitSphere n) := by
      rw [hsphere]
      exact isCompact_sphere _ _
    have hset : unitMaximal T = unitSphere n ∩ (maximalSpace T : Set (H n)) := by
      ext x
      exact and_comm
    rw [hset]
    exact hc.inter_right hmax.1

theorem gradient_nonempty_compact {n k : ℕ} (hn : 1 ≤ n)
    (T : Square n) (R : Fin k → Square n) :
    (gradientImage T R).Nonempty ∧ IsCompact (gradientImage T R) := by
  have h := unitMaximal_nonempty_compact hn T
  exact ⟨h.1.image (gradient T R), h.2.image (gradient_continuous T R)⟩

#print axioms gradient_continuous
#assert_trust kernel gradient_continuous
#print axioms unitMaximal_nonempty_compact
#assert_trust kernel unitMaximal_nonempty_compact
#print axioms gradient_nonempty_compact
#assert_trust kernel gradient_nonempty_compact

end
end NLA.IE02

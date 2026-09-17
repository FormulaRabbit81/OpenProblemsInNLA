/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 attribution is retained in
Definitions.lean and SourceCorrespondence.md. Reuses Mathlib compactness and
continuous extrema. The frozen hn and hne premises are redundant for this
stronger compact-set argument and are retained without artificial uses.
-/
import NLA.IE02.MaximalSpace
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem descent_complement_gap {n : ℕ} (hn : 1 ≤ n) (T D : Square n)
    (hne : T ≠ 0) (γ : ℝ) (hγ : 0 < γ)
    (hpos : ∀ x ∈ unitMaximal T, γ ≤ descentForm T D x)
    (hK : (descentComplement T D γ).Nonempty) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ descentComplement T D γ,
      ‖euclideanLin T x‖ ^ 2 ≤ operatorNorm T ^ 2 - β := by
  have hcontinuous : Continuous (fun x : H n => descentForm T D x) := by
    -- Expose the real inner product of the actual continuous matrix actions.
    change Continuous (fun x : H n =>
      (inner ℂ (euclideanCLM T x) (euclideanCLM D x)).re)
    fun_prop
  have hset : descentComplement T D γ =
      Metric.sphere (0 : H n) 1 ∩ {x | descentForm T D x ≤ γ / 2} := by
    ext x
    simp only [descentComplement, unitSphere, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Metric.mem_sphere, dist_zero_right]
  have hcompact : IsCompact (descentComplement T D γ) := by
    rw [hset]
    exact (isCompact_sphere (0 : H n) 1).inter_right
      (isClosed_le hcontinuous continuous_const)
  have hnormContinuous : Continuous (fun x : H n => ‖euclideanLin T x‖ ^ 2) := by
    -- The continuous extension is definitionally the same Euclidean action.
    change Continuous (fun x : H n => ‖euclideanCLM T x‖ ^ 2)
    fun_prop
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hK hnormContinuous.continuousOn
  have hxnorm : ‖x‖ = 1 := hx.1
  have hbound : ‖euclideanLin T x‖ ≤ operatorNorm T := by
    have hop : ‖euclideanLin T x‖ ≤ operatorNorm T * ‖x‖ :=
      (euclideanCLM T).le_opNorm x
    simpa only [hxnorm, mul_one] using hop
  have hstrict : ‖euclideanLin T x‖ < operatorNorm T := by
    rcases lt_or_eq_of_le hbound with hlt | heq
    · exact hlt
    · exfalso
      have hmem : x ∈ unitMaximal T := by
        refine ⟨((maximal_space_norm T).2 x).mpr ?_, hxnorm⟩
        simpa only [hxnorm, mul_one] using heq
      have hpositive := hpos x hmem
      have hsmall : descentForm T D x ≤ γ / 2 := hx.2
      linarith
  have hsquared : ‖euclideanLin T x‖ ^ 2 < operatorNorm T ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg (euclideanCLM T))).mpr hstrict
  refine ⟨operatorNorm T ^ 2 - ‖euclideanLin T x‖ ^ 2, sub_pos.mpr hsquared, ?_⟩
  intro y hy
  have hmaximum : ‖euclideanLin T y‖ ^ 2 ≤ ‖euclideanLin T x‖ ^ 2 := hmax hy
  linarith

#print axioms descent_complement_gap
#assert_trust kernel descent_complement_gap

end
end NLA.IE02

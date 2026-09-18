/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 attribution is retained in
Definitions.lean and SourceCorrespondence.md. Reuses Mathlib's closed-set nearest
point theorem in proper spaces; dependent or zero directions are allowed.
-/
import NLA.IE02.Definitions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

private theorem finite_combination_minimum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {k : ℕ} (y : E) (v : Fin k → E) :
    ∃ c : Fin k → ℂ,
      ‖y - ∑ j, c j • v j‖ = sInf (Set.range (fun d : Fin k → ℂ => ‖y - ∑ j, d j • v j‖)) ∧
      ∀ d : Fin k → ℂ, ‖y - ∑ j, c j • v j‖ ≤ ‖y - ∑ j, d j • v j‖ := by
  let L : (Fin k → ℂ) →ₗ[ℂ] E :=
    { toFun := fun c => ∑ j, c j • v j
      map_add' := by
        intro c d
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
        rfl }
  let S := LinearMap.range L
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hclosed : IsClosed (S : Set E) := S.closed_of_finiteDimensional
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist ⟨0, S.zero_mem⟩ y
  obtain ⟨c, rfl⟩ := hz
  have hmin (d : Fin k → ℂ) : ‖y - L c‖ ≤ ‖y - L d‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, ← hdist]
    -- S is the actual range of L, so d supplies the membership witness.
    exact Metric.infDist_le_dist_of_mem (show L d ∈ S from ⟨d, rfl⟩)
  have hleast : IsLeast (Set.range (fun d : Fin k → ℂ => ‖y - L d‖)) ‖y - L c‖ := by
    refine ⟨⟨c, rfl⟩, ?_⟩
    rintro _ ⟨d, rfl⟩
    exact hmin d
  exact ⟨c, hleast.csInf_eq.symm, hmin⟩

private theorem affine_operator_action {n k : ℕ} (Y : Square n)
    (R : Fin k → Square n) (c : Fin k → ℂ) :
    euclideanCLM (affineResidual Y R c) =
      euclideanCLM Y - ∑ j, c j • euclideanCLM (R j) := by
  simp only [euclideanCLM, euclideanLin, Matrix.toEuclideanLin,
    affineResidual, directionSum, map_sub, map_sum, map_smul]

theorem affine_operator_minimum {n k : ℕ} (Y : Square n) (R : Fin k → Square n) :
    ∃ c : Fin k → ℂ, operatorNorm (affineResidual Y R c) = affineIdeal Y R ∧
      ∀ d : Fin k → ℂ, operatorNorm (affineResidual Y R c) ≤ operatorNorm (affineResidual Y R d) := by
  simpa only [operatorNorm, affineIdeal, affine_operator_action] using
    finite_combination_minimum (euclideanCLM Y) (fun j => euclideanCLM (R j))

theorem affine_vector_minimum {n k : ℕ} (Y : Square n) (R : Fin k → Square n) (x : H n) :
    ∃ c : Fin k → ℂ, ‖euclideanLin (affineResidual Y R c) x‖ = affineInner Y R x ∧
      ∀ d : Fin k → ℂ, ‖euclideanLin (affineResidual Y R c) x‖ ≤
        ‖euclideanLin (affineResidual Y R d) x‖ := by
  have haction (c : Fin k → ℂ) : euclideanLin (affineResidual Y R c) x =
      euclideanLin Y x - ∑ j, c j • euclideanLin (R j) x := by
    -- The continuous extension has exactly the original Euclidean linear action.
    change euclideanCLM (affineResidual Y R c) x = _
    rw [affine_operator_action]
    simp only [_root_.sub_apply, _root_.sum_apply,
      _root_.smul_apply]
    rfl
  simpa only [affineInner, haction] using
    finite_combination_minimum (euclideanLin Y x) (fun j => euclideanLin (R j) x)

#print axioms affine_operator_minimum
#assert_trust kernel affine_operator_minimum
#print axioms affine_vector_minimum
#assert_trust kernel affine_vector_minimum

end
end NLA.IE02

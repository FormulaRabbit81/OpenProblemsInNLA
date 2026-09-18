/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A continuous definite seminorm on the concrete finite-dimensional Euclidean
space bounds the original Euclidean norm from below. Compactness supplies the
minimum on the unit sphere; homogeneity extends the bound to every vector.
No numerical mesh, dimension enumeration, or comparison oracle is used.
-/
import NLA.MF07.NormGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma definite_seminorm_bounds_norm {d : ℕ} (hd : 1 ≤ d)
    (p : Seminorm ℂ (EuclideanVector d))
    (hp : Continuous (p : EuclideanVector d → ℝ))
    (hdef : ∀ x : EuclideanVector d, p x = 0 ↔ x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanVector d, ‖x‖ ≤ c * p x := by
  have hne : (Metric.sphere (0 : EuclideanVector d) 1).Nonempty := by
    refine ⟨coordinateUnit ⟨0, by omega⟩, ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right, coordinateUnit_norm]
  obtain ⟨z, hz, hmin⟩ :=
    (isCompact_sphere (0 : EuclideanVector d) 1).exists_isMinOn hne hp.continuousOn
  have hznorm : ‖z‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have hz0 : z ≠ 0 := by
    intro h
    have h01 : (0 : ℝ) = 1 := by simpa only [h, norm_zero] using hznorm
    exact zero_ne_one h01
  have hpz : 0 < p z := by
    have hpz0 : p z ≠ 0 := fun h => hz0 ((hdef z).mp h)
    exact lt_of_le_of_ne (apply_nonneg p z) hpz0.symm
  refine ⟨(p z)⁻¹, inv_pos.mpr hpz, ?_⟩
  intro x
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero, map_zero, mul_zero, le_refl]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hunit : (‖x‖⁻¹ : ℂ) • x ∈ Metric.sphere (0 : EuclideanVector d) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hxnorm.ne']
  have hscaled0 : p z ≤ p ((‖x‖⁻¹ : ℂ) • x) := hmin hunit
  have hscaled : p z ≤ ‖x‖⁻¹ * p x := by
    simpa only [map_smul_eq_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg x)] using hscaled0
  have hmul : ‖x‖ * p z ≤ p x := by
    calc
      ‖x‖ * p z ≤ ‖x‖ * (‖x‖⁻¹ * p x) :=
        mul_le_mul_of_nonneg_left hscaled hxnorm.le
      _ = p x := by rw [← mul_assoc, mul_inv_cancel₀ hxnorm.ne', one_mul]
  calc
    ‖x‖ = (p z)⁻¹ * (‖x‖ * p z) := by
      rw [mul_left_comm, inv_mul_cancel₀ hpz.ne', mul_one]
    _ ≤ (p z)⁻¹ * p x := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hpz.le)

#print axioms definite_seminorm_bounds_norm
#assert_trust kernel definite_seminorm_bounds_norm

end NLA.MF06

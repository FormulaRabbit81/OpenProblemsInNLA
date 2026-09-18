/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The first component is the actual orthogonal projection onto the stable
kernel. The second component is the actual quotient seminorm. Their sum is
definite, and finite-dimensional compactness yields a common comparison
constant. The quotient identity is used to control the complementary vector.
These constructions also apply when the stable kernel is the zero submodule.
-/
import NLA.MF06.QuotientSeminorm
import NLA.MF06.NormCoercivity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

/-- The stable-coordinate seminorm is evaluated at the actual orthogonal projection. -/
def stableComponentSeminorm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d)) : Seminorm ℂ (EuclideanVector d) :=
  u.comp (stableKernel M hM hneM hbounded).starProjection.toLinearMap

@[simp] lemma stableComponentSeminorm_apply {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d)) (x : EuclideanVector d) :
    stableComponentSeminorm M hM hneM hbounded u x =
      u ((stableKernel M hM hneM hbounded).starProjection x) := rfl

lemma stableComponentSeminorm_continuous {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d)) (hu : Continuous (u : EuclideanVector d → ℝ)) :
    Continuous (stableComponentSeminorm M hM hneM hbounded u : EuclideanVector d → ℝ) :=
  hu.comp (stableKernel M hM hneM hbounded).starProjection.continuous

lemma stableComponentSeminorm_le {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d)) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ x : EuclideanVector d, u x ≤ C * ‖x‖) (x : EuclideanVector d) :
    stableComponentSeminorm M hM hneM hbounded u x ≤ C * ‖x‖ :=
  (hu _).trans (mul_le_mul_of_nonneg_left
    ((stableKernel M hM hneM hbounded).norm_starProjection_apply_le x) hC)

lemma stableComponentSeminorm_on_kernel {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d)) (x : EuclideanVector d)
    (hx : x ∈ stableKernel M hM hneM hbounded) :
    stableComponentSeminorm M hM hneM hbounded u x = u x := by
  rw [stableComponentSeminorm_apply,
    (stableKernel M hM hneM hbounded).starProjection_eq_self_iff.mpr hx]

lemma stableProjection_complement {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    (stableKernel M hM hneM hbounded).starProjection
      (x - (stableKernel M hM hneM hbounded).starProjection x) = 0 := by
  let S := stableKernel M hM hneM hbounded
  have hproj : S.starProjection (S.starProjection x) = S.starProjection x :=
    S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)
  change S.starProjection (x - S.starProjection x) = 0
  rw [map_sub, hproj, sub_self]

lemma stableGauge_complement {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    stableGauge M (x - (stableKernel M hM hneM hbounded).starProjection x) = stableGauge M x :=
  stableGauge_sub_kernel M hM hneM hbounded x _
    ((stableKernel M hM hneM hbounded).starProjection_apply_mem x)

lemma componentSum_definite {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d))
    (hu : ∀ x : EuclideanVector d, ‖x‖ ≤ u x) (x : EuclideanVector d) :
    (stableComponentSeminorm M hM hneM hbounded u + stableSeminorm M hM hneM hbounded) x = 0 ↔
      x = 0 := by
  let S := stableKernel M hM hneM hbounded
  change u (S.starProjection x) + stableGauge M x = 0 ↔ x = 0
  constructor
  · intro hzero
    have ha : 0 ≤ u (S.starProjection x) := apply_nonneg u _
    have hb : 0 ≤ stableGauge M x := apply_nonneg (stableSeminorm M hM hneM hbounded) x
    have hpzero : stableGauge M x = 0 := by linarith
    have hxS : x ∈ S := hpzero
    have hproj : S.starProjection x = x := S.starProjection_eq_self_iff.mpr hxS
    rw [hproj, hpzero, add_zero] at hzero
    exact norm_eq_zero.mp (le_antisymm ((hu x).trans_eq hzero) (norm_nonneg x))
  · intro hx
    subst x
    change (stableComponentSeminorm M hM hneM hbounded u + stableSeminorm M hM hneM hbounded) 0 = 0
    exact map_zero _

/-- The same fixed constant bounds both the whole vector in the component-sum
norm and its complementary vector in the actual quotient norm alone. -/
lemma component_norm_bounds {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d)) (hu : Continuous (u : EuclideanVector d → ℝ))
    (hlower : ∀ x : EuclideanVector d, ‖x‖ ≤ u x) :
    ∃ c : ℝ, 0 < c ∧
      (∀ x : EuclideanVector d,
        ‖x‖ ≤ c * (stableComponentSeminorm M hM hneM hbounded u x + stableGauge M x)) ∧
      (∀ x : EuclideanVector d,
        ‖x - (stableKernel M hM hneM hbounded).starProjection x‖ ≤ c * stableGauge M x) := by
  let a := stableComponentSeminorm M hM hneM hbounded u
  let p := stableSeminorm M hM hneM hbounded
  have hcont : Continuous ((a + p) : EuclideanVector d → ℝ) :=
    (stableComponentSeminorm_continuous M hM hneM hbounded u hu).add
      (stableGauge_continuous M hM hneM hbounded)
  obtain ⟨c, hc, hbound⟩ := definite_seminorm_bounds_norm hd (a + p) hcont
    (componentSum_definite M hM hneM hbounded u hlower)
  refine ⟨c, hc, hbound, ?_⟩
  intro x
  have hx := hbound (x - (stableKernel M hM hneM hbounded).starProjection x)
  change ‖x - (stableKernel M hM hneM hbounded).starProjection x‖ ≤
    c * (u ((stableKernel M hM hneM hbounded).starProjection
      (x - (stableKernel M hM hneM hbounded).starProjection x)) +
      stableGauge M (x - (stableKernel M hM hneM hbounded).starProjection x)) at hx
  simpa only [stableProjection_complement M hM hneM hbounded,
    stableGauge_complement M hM hneM hbounded, map_zero, zero_add] using hx

#print axioms componentSum_definite
#assert_trust kernel componentSum_definite
#print axioms component_norm_bounds
#assert_trust kernel component_norm_bounds

end NLA.MF06

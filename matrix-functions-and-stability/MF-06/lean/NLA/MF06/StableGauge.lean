/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The actual decreasing tails converge to the frozen infimum. Passing their
triangle and homogeneity laws to the limit gives a Mathlib seminorm. Domination
by the envelope gives continuity; Mathlib's Dini theorem gives compact-uniform
convergence without discretizing vectors, word sets or the compact family.
-/
import NLA.MF06.TailEnvelope

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 Filter Topology

lemma stableGauge_triangle {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x y : EuclideanVector d) :
    stableGauge M (x + y) ≤ stableGauge M x + stableGauge M y := by
  exact le_of_tendsto_of_tendsto'
    (tailEnvelope_tendsto M hM hneM hbounded (x + y))
    ((tailEnvelope_tendsto M hM hneM hbounded x).add
      (tailEnvelope_tendsto M hM hneM hbounded y))
    (fun n => tailEnvelope_triangle M hM hneM hbounded n x y)

lemma stableGauge_smul {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (c : ℂ) (x : EuclideanVector d) :
    stableGauge M (c • x) = ‖c‖ * stableGauge M x := by
  have hscaled : Tendsto (fun n : ℕ => tailEnvelope M n (c • x)) atTop
      (𝓝 (‖c‖ * stableGauge M x)) := by
    simpa only [tailEnvelope_smul M hM hneM hbounded] using
      (tailEnvelope_tendsto M hM hneM hbounded x).const_mul ‖c‖
  exact tendsto_nhds_unique (tailEnvelope_tendsto M hM hneM hbounded (c • x)) hscaled

/-- A genuine Mathlib seminorm whose value is definitionally the prescribed infimum. -/
def stableSeminorm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    Seminorm ℂ (EuclideanVector d) :=
  Seminorm.of (stableGauge M)
    (stableGauge_triangle M hM hneM hbounded)
    (stableGauge_smul M hM hneM hbounded)

@[simp] lemma stableSeminorm_apply {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    stableSeminorm M hM hneM hbounded x = stableGauge M x := rfl

lemma stableGauge_le_boundedEnvelope {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) : stableGauge M x ≤ boundedEnvelope M x := by
  exact le_of_tendsto_of_tendsto' (tailEnvelope_tendsto M hM hneM hbounded x)
    tendsto_const_nhds (fun n => tailEnvelope_le_boundedEnvelope M hM hneM hbounded n x)

lemma stableGauge_continuous {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    Continuous (stableGauge M) := by
  change Continuous (stableSeminorm M hM hneM hbounded : EuclideanVector d → ℝ)
  apply Seminorm.continuous_of_le (q := boundedEnvelopeSeminorm M hM hneM hbounded)
  · exact (bounded_envelope_norm M hM hneM hbounded).2.1
  · intro x
    exact stableGauge_le_boundedEnvelope M hM hneM hbounded x

/-- C06: all actual tails converge uniformly on every compact set, including
when the limiting seminorm vanishes identically. -/
theorem tail_seminorm_limit {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    (∀ n : ℕ, Continuous (tailEnvelope M n)) ∧
    (∀ x : EuclideanVector d, Antitone (fun n : ℕ => tailEnvelope M n x)) ∧
    (∃ p : Seminorm ℂ (EuclideanVector d), ∀ x, p x = stableGauge M x) ∧
    Continuous (stableGauge M) ∧
    (∀ x : EuclideanVector d, stableGauge M x ≤ boundedEnvelope M x) ∧
    (∀ K : Set (EuclideanVector d), IsCompact K →
      TendstoUniformlyOn (tailEnvelope M) (stableGauge M) atTop K) := by
  refine ⟨tailEnvelope_continuous M hM hneM hbounded,
    tailEnvelope_antitone M hM hneM hbounded,
    ⟨stableSeminorm M hM hneM hbounded, fun _ => rfl⟩,
    stableGauge_continuous M hM hneM hbounded,
    stableGauge_le_boundedEnvelope M hM hneM hbounded, ?_⟩
  intro K hK
  exact Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun n => (tailEnvelope_continuous M hM hneM hbounded n).continuousOn)
    (fun x _ => tailEnvelope_antitone M hM hneM hbounded x)
    (stableGauge_continuous M hM hneM hbounded).continuousOn
    (fun x _ => tailEnvelope_tendsto M hM hneM hbounded x)

#print axioms tail_seminorm_limit
#assert_trust kernel tail_seminorm_limit

end NLA.MF06

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The kernel is constructed from the already proved Mathlib seminorm. Uniform
tail convergence on a subspace's compact unit ball gives one common small
tail for every unit vector; no basis enumeration or nonzero-subspace premise
is needed. Properness and the exponential bound are proved in a later module.
-/
import NLA.MF06.MaxRecurrence
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 Filter Topology

/-- The literal zero set of the limit seminorm as a complex submodule. -/
def stableKernel {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    Submodule ℂ (EuclideanVector d) where
  carrier := {x | stableGauge M x = 0}
  zero_mem' := map_zero (stableSeminorm M hM hneM hbounded)
  add_mem' := by
    intro x y hx hy
    apply le_antisymm _ (apply_nonneg (stableSeminorm M hM hneM hbounded) (x + y))
    calc
      stableGauge M (x + y) ≤ stableGauge M x + stableGauge M y :=
        stableGauge_triangle M hM hneM hbounded x y
      _ = 0 := by rw [hx, hy, zero_add]
  smul_mem' := by
    intro c x hx
    change stableGauge M (c • x) = 0
    rw [stableGauge_smul M hM hneM hbounded, hx, mul_zero]

@[simp] lemma mem_stableKernel {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    x ∈ stableKernel M hM hneM hbounded ↔ stableGauge M x = 0 := Iff.rfl

lemma stableKernel_invariant {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    FamilyInvariant M (stableKernel M hM hneM hbounded) := by
  intro A hA x hx
  change stableGauge M (applyMatrix A x) = 0
  apply le_antisymm _ (apply_nonneg (stableSeminorm M hM hneM hbounded) (applyMatrix A x))
  exact (stableGauge_generator_le M hM hneM hbounded A hA x).trans_eq hx

/-- Generator invariance propagates through the actual chronological products. -/
lemma familyInvariant_word {d : ℕ} (M : Set (Square d))
    (S : Submodule ℂ (EuclideanVector d)) (hS : FamilyInvariant M S)
    (w : List (Square d)) (hw : WordIn M w) (x : EuclideanVector d) (hx : x ∈ S) :
    applyMatrix (matrixProduct w) x ∈ S := by
  induction w generalizing x with
  | nil => simpa only [matrixProduct_nil, applyMatrix_one] using hx
  | cons A w ih =>
      obtain ⟨hA, hw⟩ := (WordIn_cons_iff M A w).mp hw
      rw [matrixProduct_cons, applyMatrix_mul]
      exact ih hw (applyMatrix A x) (hS A hA x hx)

/-- A single tail index controls every unit vector of an arbitrary subspace
on which the actual limit vanishes. The conclusion also holds for S = bottom. -/
lemma uniform_small_tail_on_subspace {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (S : Submodule ℂ (EuclideanVector d))
    (hzero : ∀ x : EuclideanVector d, x ∈ S → stableGauge M x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ x : EuclideanVector d, x ∈ S → ‖x‖ = 1 → tailEnvelope M n x ≤ ε := by
  let K : Set (EuclideanVector d) := Metric.closedBall 0 1 ∩ (S : Set (EuclideanVector d))
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : EuclideanVector d) 1).inter_right
      (Submodule.closed_of_finiteDimensional S)
  have hlim := (tail_seminorm_limit M hM hneM hbounded).2.2.2.2.2 K hK
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hlim) ε hε)
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn x hx hnorm
  have hxK : x ∈ K := ⟨by
    simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using (le_rfl : (1 : ℝ) ≤ 1), hx⟩
  have hdist := hN n ((le_max_right 1 N).trans hn) x hxK
  have htail : tailEnvelope M n x < ε := by
    simpa only [hzero x hx, dist_zero_left, Real.norm_eq_abs,
      abs_of_nonneg (tailEnvelope_nonneg M hM hneM hbounded n x)] using hdist
  exact htail.le

#print axioms stableKernel_invariant
#assert_trust kernel stableKernel_invariant
#print axioms uniform_small_tail_on_subspace
#assert_trust kernel uniform_small_tail_on_subspace

end NLA.MF06

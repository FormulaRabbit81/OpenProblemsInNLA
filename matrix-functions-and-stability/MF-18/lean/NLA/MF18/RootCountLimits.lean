/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

All roots are placed in one finite-dimensional compact ball. A convergent
subsequence identifies the limiting root multiset through its full product.
No multiplicity is inferred from mere proximity to the set of distinct roots.
-/
import NLA.MF18.RootProductLimits
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators Topology NNReal

noncomputable section
namespace NLA.MF18

theorem root_enumerations_uniformly_bounded {N : ℕ} (p : ℕ → CPoly) (p₀ : CPoly)
    (hp : ∀ k, (p k).Monic) (hd : ∀ k, (p k).natDegree = N)
    (hc : ∀ j, Filter.Tendsto (fun k => (p k).coeff j) Filter.atTop (nhds (p₀.coeff j)))
    (r : ℕ → Fin N → ℂ) (hr : ∀ k, Finset.univ.val.map (r k) = (p k).roots) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k, ‖r k‖ ≤ R := by
  let a : ℕ → Fin N → ℂ := fun k j => (p k).coeff j
  let a₀ : Fin N → ℂ := fun j => p₀.coeff j
  have ha : Filter.Tendsto a Filter.atTop (nhds a₀) :=
    tendsto_pi_nhds.mpr fun j => hc j
  obtain ⟨R, hR, hbound⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  let M : ℝ≥0 := ⟨R, hR.le⟩
  refine ⟨R + 1, by positivity, fun k => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ R + 1)).mpr
  intro i
  have hcoeff : ∀ j < (p k).natDegree, ‖(p k).coeff j‖₊ ≤ M := by
    intro j hj
    have hj' : j < N := by simpa only [hd k] using hj
    have hn : ‖(p k).coeff j‖ ≤ R :=
      (norm_le_pi_norm (a k) ⟨j, hj'⟩).trans (hbound (a k) (Set.mem_range_self k))
    exact_mod_cast hn
  have hnorm := monic_root_norm_bound (p k) (hp k) M hcoeff (r k i)
    (isRoot_of_root_enumeration (p k) (r k) (hr k) i)
  exact_mod_cast hnorm.le

theorem halfPlane_count_eventually_of_coeff_tendsto {N : ℕ} (p : ℕ → CPoly) (p₀ : CPoly)
    (hp : ∀ k, (p k).Monic) (hd : ∀ k, (p k).natDegree = N) (hd₀ : p₀.natDegree ≤ N)
    (hc : ∀ j, Filter.Tendsto (fun k => (p k).coeff j) Filter.atTop (nhds (p₀.coeff j)))
    (hb : ∀ z : ℂ, z.re = 0 → p₀.eval z ≠ 0) :
    ∀ᶠ k in Filter.atTop, rightHalfPlaneRootCount (p k) = rightHalfPlaneRootCount p₀ := by
  classical
  choose r hr using fun k => exists_roots_enumeration (p k) N (hd k)
  obtain ⟨R, hR, hbound⟩ := root_enumerations_uniformly_bounded p p₀ hp hd hc r hr
  by_contra hne
  obtain ⟨ψ, hψ, hbad⟩ := Filter.exists_seq_forall_of_frequently (Filter.not_eventually.mp hne)
  have hball : ∀ k, r (ψ k) ∈ Metric.closedBall (0 : Fin N → ℂ) R := by
    intro k
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound (ψ k)
  obtain ⟨r₀, _, φ, hφ, hrlim⟩ := (isCompact_closedBall (0 : Fin N → ℂ) R).tendsto_subseq hball
  have hcomp : Filter.Tendsto (fun k => ψ (φ k)) Filter.atTop Filter.atTop :=
    hψ.comp hφ.tendsto_atTop
  have hprod₀ : p₀ = ∏ i : Fin N, (Polynomial.X - Polynomial.C (r₀ i)) :=
    product_limit_of_coeff_limit (fun k => p (ψ (φ k))) p₀
      (fun k => (hd (ψ (φ k))).le) hd₀ (fun j => (hc j).comp hcomp)
      (fun k => r (ψ (φ k))) r₀
      (fun k => monic_eq_prod_root_enumeration (p (ψ (φ k))) (hp (ψ (φ k)))
        (r (ψ (φ k))) (hr (ψ (φ k)))) hrlim
  have hr₀ : Finset.univ.val.map r₀ = p₀.roots := by
    rw [hprod₀]
    exact (roots_of_prod_root_enumeration r₀).symm
  have hnz : ∀ i, (r₀ i).re ≠ 0 := by
    intro i hi
    exact hb (r₀ i) hi (isRoot_of_root_enumeration p₀ r₀ hr₀ i)
  obtain ⟨k, hk⟩ := (eventually_halfPlane_index_count_eq
    (fun k => r (ψ (φ k))) r₀ hrlim hnz).exists
  apply hbad (φ k)
  calc
    rightHalfPlaneRootCount (p (ψ (φ k))) =
        (Finset.univ.filter (fun i : Fin N => 0 < (r (ψ (φ k)) i).re)).card :=
      halfPlane_count_root_enumeration (p (ψ (φ k))) (r (ψ (φ k))) (hr (ψ (φ k)))
    _ = (Finset.univ.filter (fun i : Fin N => 0 < (r₀ i).re)).card := hk
    _ = rightHalfPlaneRootCount p₀ := (halfPlane_count_root_enumeration p₀ r₀ hr₀).symm

#print axioms root_enumerations_uniformly_bounded
#print axioms halfPlane_count_eventually_of_coeff_tendsto

end NLA.MF18

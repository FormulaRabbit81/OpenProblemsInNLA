/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.RootCountLimits
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false
open scoped Topology

noncomputable section
namespace NLA.MF18

theorem monic_half_plane_count_homotopy (N : ℕ) (q : ℝ → CPoly)
    (hc : CoeffContinuousOn q (Set.Icc 0 1))
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, (q t).Monic ∧ (q t).natDegree = N)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, z.re = 0 → (q t).eval z ≠ 0) :
    rightHalfPlaneRootCount (q 0) = rightHalfPlaneRootCount (q 1) := by
  have hcont : Continuous (fun t : Set.Icc (0 : ℝ) 1 => rightHalfPlaneRootCount (q t)) := by
    apply SeqContinuous.continuous
    intro s a hs
    have hcoeff : ∀ j, Filter.Tendsto (fun k => (q (s k)).coeff j) Filter.atTop
        (nhds ((q a).coeff j)) := by
      intro j
      exact ((hc j).domRestrict.tendsto a).comp hs
    have hevent := halfPlane_count_eventually_of_coeff_tendsto
      (fun k => q (s k)) (q a)
      (fun k => (hm (s k) (s k).property).1)
      (fun k => (hm (s k) (s k).property).2)
      (hm a a.property).2.le hcoeff (hb a a.property)
    exact (Filter.tendsto_congr' hevent).mpr tendsto_const_nhds
  have hconton : ContinuousOn (fun t : ℝ => rightHalfPlaneRootCount (q t)) (Set.Icc 0 1) :=
    continuousOn_iff_continuous_domRestrict.mpr hcont
  exact isPreconnected_Icc.constant hconton (by simp) (by simp)

#print axioms monic_half_plane_count_homotopy

end NLA.MF18

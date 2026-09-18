/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

The limit argument uses the complete characteristic-polynomial root multiset:
for a point outside the unit disk, every factor stays uniformly away from zero.
It needs neither continuous root labels nor a positive dimension assumption.
-/
import NLA.MF18.Definitions
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FunProp

set_option autoImplicit false
open scoped BigOperators Topology

noncomputable section
namespace NLA.MF18

private theorem monic_eval_norm_lower_bound (p : CPoly) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) (lam : ℂ) (hlam : 1 ≤ ‖lam‖) :
    (‖lam‖ - 1) ^ p.natDegree ≤ ‖p.eval lam‖ := by
  classical
  calc
    (‖lam‖ - 1) ^ p.natDegree =
        (p.roots.map fun _ => ‖lam‖ - 1).prod := by
      simp only [Multiset.map_const', Multiset.prod_replicate,
        IsAlgClosed.card_roots_eq_natDegree]
    _ ≤ (p.roots.map fun z => ‖lam - z‖).prod := by
      apply Multiset.prod_map_le_prod_map₀
      · intro z hz
        exact sub_nonneg.mpr hlam
      · intro z hz
        calc
          ‖lam‖ - 1 ≤ ‖lam‖ - ‖z‖ := sub_le_sub_left (hroots z hz) _
          _ ≤ ‖lam - z‖ := norm_sub_norm_le lam z
    _ = ‖p.eval lam‖ := by
      rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp]
      exact p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun z => lam - z)

theorem closed_disk_stability_limit {n : ℕ} (S : ℕ → Mat n) (S₀ : Mat n)
    (hlim : Filter.Tendsto S Filter.atTop (nhds S₀))
    (hs : ∀ k : ℕ, StrictStable (S k)) : WeakStable S₀ := by
  intro lam hroot
  by_contra! hbad
  have hc : Continuous (fun A : Mat n => A.charpoly.eval lam) := by
    simp_rw [Matrix.eval_charpoly]
    fun_prop
  have ht : Filter.Tendsto (fun k => (S k).charpoly.eval lam)
      Filter.atTop (nhds (S₀.charpoly.eval lam)) := (hc.tendsto S₀).comp hlim
  have hle : (‖lam‖ - 1) ^ n ≤ ‖S₀.charpoly.eval lam‖ := by
    apply ge_of_tendsto' ht.norm
    intro k
    have hk := monic_eval_norm_lower_bound (S k).charpoly (S k).charpoly_monic
      (fun z hz => (hs k z (Polynomial.isRoot_of_mem_roots hz)).le) lam hbad.le
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using hk
  have hp : 0 < (‖lam‖ - 1) ^ n := pow_pos (sub_pos.mpr hbad) n
  have hz : S₀.charpoly.eval lam = 0 := hroot
  rw [hz, norm_zero] at hle
  exact (not_lt_of_ge hle) hp

#print axioms closed_disk_stability_limit

end NLA.MF18

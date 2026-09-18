/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Finite-product convergence records every root, including multiplicities.
No choice of root labels is assumed continuous before taking a subsequence.
-/
import NLA.MF18.RootEnumeration
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.Finite

set_option autoImplicit false
open scoped BigOperators Topology

noncomputable section
namespace NLA.MF18

theorem eval_tendsto_of_coeff_tendsto (N : ℕ) (p : ℕ → CPoly) (p₀ : CPoly)
    (hd : ∀ k, (p k).natDegree ≤ N) (hd₀ : p₀.natDegree ≤ N)
    (hc : ∀ j, Filter.Tendsto (fun k => (p k).coeff j) Filter.atTop (nhds (p₀.coeff j)))
    (z : ℂ) : Filter.Tendsto (fun k => (p k).eval z) Filter.atTop (nhds (p₀.eval z)) := by
  have he (k : ℕ) := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hd k)) z
  have he₀ := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd₀) z
  simp_rw [he, he₀]
  exact tendsto_finsetSum _ fun j _ => (hc j).mul_const (z ^ j)

theorem product_limit_of_coeff_limit {N : ℕ} (p : ℕ → CPoly) (p₀ : CPoly)
    (hd : ∀ k, (p k).natDegree ≤ N) (hd₀ : p₀.natDegree ≤ N)
    (hc : ∀ j, Filter.Tendsto (fun k => (p k).coeff j) Filter.atTop (nhds (p₀.coeff j)))
    (r : ℕ → Fin N → ℂ) (r₀ : Fin N → ℂ)
    (hprod : ∀ k, p k = ∏ i : Fin N, (Polynomial.X - Polynomial.C (r k i)))
    (hr : Filter.Tendsto r Filter.atTop (nhds r₀)) :
    p₀ = ∏ i : Fin N, (Polynomial.X - Polynomial.C (r₀ i)) := by
  apply Polynomial.funext
  intro z
  have hp := eval_tendsto_of_coeff_tendsto N p p₀ hd hd₀ hc z
  have he : (fun k => (p k).eval z) = (fun k => ∏ i : Fin N, (z - r k i)) := by
    funext k
    simp only [hprod k, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  rw [he] at hp
  have hp' : Filter.Tendsto (fun k => ∏ i : Fin N, (z - r k i)) Filter.atTop
      (nhds (∏ i : Fin N, (z - r₀ i))) :=
    tendsto_finsetProd _ fun i _ => tendsto_const_nhds.sub (hr.apply_nhds i)
  simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using tendsto_nhds_unique hp hp'

theorem roots_of_prod_root_enumeration {N : ℕ} (r : Fin N → ℂ) :
    (∏ i : Fin N, (Polynomial.X - Polynomial.C (r i))).roots = Finset.univ.val.map r := by
  calc
    (∏ i : Fin N, (Polynomial.X - Polynomial.C (r i))).roots =
        ((Finset.univ.val.map r).map (fun z => Polynomial.X - Polynomial.C z)).prod.roots := by
      congr 1
      rw [Multiset.map_map]
      rfl
    _ = Finset.univ.val.map r := Polynomial.roots_multiset_prod_X_sub_C _

theorem eventually_halfPlane_index_count_eq {N : ℕ} (r : ℕ → Fin N → ℂ) (r₀ : Fin N → ℂ)
    (hr : Filter.Tendsto r Filter.atTop (nhds r₀)) (hnz : ∀ i, (r₀ i).re ≠ 0) :
    ∀ᶠ k in Filter.atTop,
      (Finset.univ.filter (fun i : Fin N => 0 < (r k i).re)).card =
        (Finset.univ.filter (fun i : Fin N => 0 < (r₀ i).re)).card := by
  classical
  have hsign : ∀ i : Fin N, ∀ᶠ k in Filter.atTop,
      (0 < (r k i).re ↔ 0 < (r₀ i).re) := by
    intro i
    have ht := Complex.continuous_re.continuousAt.tendsto.comp (hr.apply_nhds i)
    rcases lt_or_gt_of_ne (hnz i) with hneg | hpos
    · filter_upwards [ht.eventually_lt_const hneg] with k hk
      exact iff_of_false (not_lt_of_gt hk) (not_lt_of_gt hneg)
    · filter_upwards [ht.eventually_const_lt hpos] with k hk
      exact iff_of_true hk hpos
  filter_upwards [Filter.eventually_all.mpr hsign] with k hk
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hk i]

#print axioms eval_tendsto_of_coeff_tendsto
#print axioms product_limit_of_coeff_limit
#print axioms roots_of_prod_root_enumeration
#print axioms eventually_halfPlane_index_count_eq

end NLA.MF18

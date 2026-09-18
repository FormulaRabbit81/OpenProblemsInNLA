/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A cross-cut product of finite sums is bounded by the pair-separation
hypothesis and two ordinary geometric series. Injectivity of the finite
exponent maps justifies the series bounds; all parameters stay symbolic.
-/
import NLA.MF06.Definitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06

lemma finite_geometric_image_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (hinj : Set.InjOn f (s : Set ι))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ i ∈ s, q ^ f i ≤ (1 - q)⁻¹ := by
  rw [← Finset.sum_image hinj]
  calc
    (∑ k ∈ s.image f, q ^ k) ≤ ∑' k : ℕ, q ^ k :=
      (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun k _ => pow_nonneg hq0 k)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

def scalarPrefix {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i

def scalarSuffix {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), x i

lemma scalar_cut_product_bound (n : ℕ) (x : Fin n → ℝ) (F q : ℝ)
    (hF : 0 ≤ F) (hq0 : 0 < q) (hq1 : q < 1)
    (hpair : ∀ i j : Fin n, i ≠ j →
      x i * x j ≤ F * q ^ (max i.val j.val - min i.val j.val)) (k : ℕ) :
    scalarPrefix x k * scalarSuffix x k ≤ F * q / (1 - q) ^ 2 := by
  let L := Finset.univ.filter (fun i : Fin n => i.val < k)
  let R := Finset.univ.filter (fun i : Fin n => k ≤ i.val)
  let f := fun i : Fin n => k - 1 - i.val
  let g := fun j : Fin n => j.val - k
  have hf : Set.InjOn f (L : Set (Fin n)) := by
    intro i hi j hj hij
    have hi' : i.val < k := (Finset.mem_filter.mp hi).2
    have hj' : j.val < k := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    dsimp only [f] at hij
    omega
  have hg : Set.InjOn g (R : Set (Fin n)) := by
    intro i hi j hj hij
    have hi' : k ≤ i.val := (Finset.mem_filter.mp hi).2
    have hj' : k ≤ j.val := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    dsimp only [g] at hij
    omega
  have hleft := finite_geometric_image_sum L f hf q hq0.le hq1
  have hright := finite_geometric_image_sum R g hg q hq0.le hq1
  have hright0 : 0 ≤ ∑ j ∈ R, q ^ g j := Finset.sum_nonneg (fun j _ => pow_nonneg hq0.le _)
  have hFq : 0 ≤ F * q := mul_nonneg hF hq0.le
  have hinv : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
  have hentry (i : Fin n) (hi : i ∈ L) (j : Fin n) (hj : j ∈ R) :
      x i * x j ≤ (F * q) * (q ^ f i * q ^ g j) := by
    have hi' : i.val < k := (Finset.mem_filter.mp hi).2
    have hj' : k ≤ j.val := (Finset.mem_filter.mp hj).2
    have hij : i ≠ j := by intro h; subst j; omega
    have hijle : i.val ≤ j.val := by omega
    have hexp : max i.val j.val - min i.val j.val = f i + 1 + g j := by
      rw [max_eq_right hijle, min_eq_left hijle]
      dsimp only [f, g]
      omega
    calc
      x i * x j ≤ F * q ^ (max i.val j.val - min i.val j.val) := hpair i j hij
      _ = (F * q) * (q ^ f i * q ^ g j) := by
        simp only [hexp, pow_add, pow_one]
        ring
  calc
    scalarPrefix x k * scalarSuffix x k = ∑ i ∈ L, ∑ j ∈ R, x i * x j := by
      change (∑ i ∈ L, x i) * (∑ j ∈ R, x j) = _
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ i ∈ L, ∑ j ∈ R, (F * q) * (q ^ f i * q ^ g j) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hentry i hi j hj))
    _ = (F * q) * (∑ i ∈ L, q ^ f i) * (∑ j ∈ R, q ^ g j) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    _ ≤ (F * q) * (1 - q)⁻¹ * (1 - q)⁻¹ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hleft hFq) hright hright0 (mul_nonneg hFq hinv)
    _ = F * q / (1 - q) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]
      ring

#print axioms scalar_cut_product_bound
#assert_trust kernel scalar_cut_product_bound

end NLA.MF06

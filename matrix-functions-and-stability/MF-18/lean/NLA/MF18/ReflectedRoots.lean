/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Fixed-grade reflection sends every nonzero root to its reciprocal, preserves
multiplicity, and inserts N-degree(p) zero roots. Zero original roots give
constant reflected factors and are explicitly included in the accounting.
-/
import NLA.MF18.ReflectionAlgebra
import NLA.MF18.RootEnumeration
import NLA.MF18.SolutionPolynomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem reflect_root_factorization (N : ℕ) (p : CPoly) (hd : p.natDegree ≤ N)
    (r : Fin p.natDegree → ℂ) (hr : Finset.univ.val.map r = p.roots) :
    p.reflect N = Polynomial.C p.leadingCoeff *
      (Polynomial.X ^ (N - p.natDegree) *
        ∏ i : Fin p.natDegree, (1 - Polynomial.C (r i) * Polynomial.X)) := by
  classical
  have heq : p = Polynomial.C p.leadingCoeff *
      ∏ i : Fin p.natDegree, (Polynomial.X - Polynomial.C (r i)) := by
    have he := (IsAlgClosed.splits p).eq_prod_roots
    rw [← hr, Multiset.map_map] at he
    exact he
  have hpdeg : (∏ i : Fin p.natDegree,
      (Polynomial.X - Polynomial.C (r i))).natDegree ≤ p.natDegree := by
    simp only [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin, le_refl]
  have hpad := Polynomial.reflect_mul (1 : CPoly)
    (∏ i : Fin p.natDegree, (Polynomial.X - Polynomial.C (r i)))
    (F := N - p.natDegree) (G := p.natDegree) (by simp) hpdeg
  rw [Nat.sub_add_cancel hd, one_mul, Polynomial.reflect_one] at hpad
  have hprod := reflect_finset_prod (Finset.univ : Finset (Fin p.natDegree))
    (fun i => (Polynomial.X - Polynomial.C (r i) : CPoly)) 1 (by intro i _; simp)
  simp only [Nat.one_mul, Finset.card_univ, Fintype.card_fin,
    Polynomial.reflect_sub, Polynomial.reflect_one_X, Polynomial.reflect_C, pow_one] at hprod
  calc
    p.reflect N = (Polynomial.C p.leadingCoeff *
        ∏ i : Fin p.natDegree, (Polynomial.X - Polynomial.C (r i))).reflect N :=
      congrArg (Polynomial.reflect N) heq
    _ = _ := by rw [Polynomial.reflect_C_mul, hpad, hprod]

theorem diskRootCount_prod {ι : Type*} (s : Finset ι) (p : ι → CPoly)
    (hp : ∀ i ∈ s, p i ≠ 0) :
    diskRootCount (∏ i ∈ s, p i) = ∑ i ∈ s, diskRootCount (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [diskRootCount]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, p j ≠ 0 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, diskRootCount_mul _ _
      (mul_ne_zero (hp i (Finset.mem_insert_self i s)) (Finset.prod_ne_zero_iff.mpr hs)), ih hs]

theorem diskRootCount_X_pow (k : ℕ) : diskRootCount (Polynomial.X ^ k : CPoly) = k := by
  classical
  unfold diskRootCount
  rw [Polynomial.roots_X_pow, Multiset.nsmul_singleton]
  rw [Multiset.filter_eq_self.mpr ?_, Multiset.card_replicate]
  intro z hz
  have hz0 : z = 0 := Multiset.eq_of_mem_replicate hz
  simp only [hz0, norm_zero, zero_lt_one]

theorem reciprocal_linear_ne_zero (a : ℂ) : (1 - Polynomial.C a * Polynomial.X : CPoly) ≠ 0 := by
  intro hz
  have he := congrArg (Polynomial.eval (0 : ℂ)) hz
  simpa using he

theorem reciprocal_linear_disk_count (a : ℂ) :
    diskRootCount (1 - Polynomial.C a * Polynomial.X : CPoly) = if 1 < ‖a‖ then 1 else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, diskRootCount]
  have heq : (1 - Polynomial.C a * Polynomial.X : CPoly) =
      Polynomial.C (-a) * (Polynomial.X - Polynomial.C a⁻¹) := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    field_simp [ha] <;> ring
  rw [heq, diskRootCount_C_mul (-a) (neg_ne_zero.mpr ha)]
  unfold diskRootCount
  rw [Polynomial.roots_X_sub_C]
  have hiff : ‖a⁻¹‖ < 1 ↔ 1 < ‖a‖ := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr ha)]
  rw [Multiset.filter_singleton]
  by_cases hlarge : 1 < ‖a‖
  · rw [if_pos (hiff.mpr hlarge), if_pos hlarge, Multiset.card_singleton]
  · rw [if_neg (mt hiff.mp hlarge), if_neg hlarge]
    rfl

theorem outside_count_root_enumeration {d : ℕ} (p : CPoly) (r : Fin d → ℂ)
    (hr : Finset.univ.val.map r = p.roots) :
    (p.roots.filter (fun z : ℂ => 1 < ‖z‖)).card =
      ∑ i : Fin d, if 1 < ‖r i‖ then 1 else 0 := by
  classical
  rw [← hr, Multiset.filter_map, Multiset.card_map]
  -- A finset cardinal is the cardinal of its underlying multiset; expose the filtered index finset.
  change (Finset.univ.filter (fun i : Fin d => 1 < ‖r i‖)).card = _
  exact (Finset.sum_boole (fun i : Fin d => 1 < ‖r i‖) Finset.univ).symm

theorem reflected_zero_and_disk_count (N : ℕ) (p : CPoly) (hp : p ≠ 0)
    (hd : p.natDegree ≤ N) :
    (p.reflect N).rootMultiplicity 0 = N - p.natDegree ∧
    diskRootCount (p.reflect N) = N - p.natDegree +
      (p.roots.filter (fun z : ℂ => 1 < ‖z‖)).card := by
  classical
  obtain ⟨r, hr⟩ := exists_roots_enumeration p p.natDegree rfl
  let q : CPoly := ∏ i : Fin p.natDegree, (1 - Polynomial.C (r i) * Polynomial.X)
  have hqeval : q.eval 0 = 1 := by
    dsimp only [q]
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_zero, sub_zero, Finset.prod_const_one]
  have hq : q ≠ 0 := by
    intro hz
    simpa [hz] using hqeval
  have hqmult : q.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    -- The non-root premise unfolds to nonzero evaluation at zero, already computed by hqeval.
    change q.eval 0 ≠ 0
    rw [hqeval]
    exact one_ne_zero)
  have hX : (Polynomial.X ^ (N - p.natDegree) : CPoly) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hC : Polynomial.C p.leadingCoeff ≠ 0 := Polynomial.C_ne_zero.mpr hlead
  have hfactor := reflect_root_factorization N p hd r hr
  -- Fold only the local abbreviation q for the reciprocal-factor product in the factorization.
  change p.reflect N = Polynomial.C p.leadingCoeff *
    (Polynomial.X ^ (N - p.natDegree) * q) at hfactor
  constructor
  · rw [hfactor, Polynomial.rootMultiplicity_mul (mul_ne_zero hC (mul_ne_zero hX hq)),
      Polynomial.rootMultiplicity_C, zero_add,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hX hq), hqmult, add_zero]
    simpa only [Polynomial.C_0, sub_zero] using
      Polynomial.rootMultiplicity_X_sub_C_pow (0 : ℂ) (N - p.natDegree)
  · rw [hfactor, diskRootCount_C_mul _ hlead,
      diskRootCount_mul _ _ (mul_ne_zero hX hq), diskRootCount_X_pow]
    congr 1
    -- Expand q back to its finite product so diskRootCount_prod applies to its actual factors.
    change diskRootCount (∏ i : Fin p.natDegree,
      (1 - Polynomial.C (r i) * Polynomial.X)) = _
    rw [diskRootCount_prod _ _ (fun i _ => reciprocal_linear_ne_zero (r i)),
      outside_count_root_enumeration p r hr]
    apply Finset.sum_congr rfl
    intro i _
    exact reciprocal_linear_disk_count (r i)

#print axioms reflected_zero_and_disk_count

end NLA.MF18

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

The exact factorization accounts for every root with its multiplicity.
A grade drop introduces N - deg(p) roots at -1, which lie outside the
counted right half-plane. No generic-leading-coefficient premise is used.
-/
import NLA.MF18.CayleyBoundary
import NLA.MF18.RootProductLimits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

private theorem cayley_linear_factor (z a : ℂ) (hz : z + 1 ≠ 0) (ha : a ≠ 1) :
    (z - 1) / (z + 1) - a = ((1 - a) / (z + 1)) * (z - (1 + a) / (1 - a)) := by
  have h1a : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  field_simp [hz, h1a] <;> ring

private theorem eval_eq_prod_root_enumeration {N : ℕ} (p : CPoly)
    (r : Fin N → ℂ) (hr : Finset.univ.val.map r = p.roots) (z : ℂ) :
    p.eval z = p.leadingCoeff * ∏ i : Fin N, (z - r i) := by
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots, ← hr, Multiset.map_map]
  rfl

theorem monicCayley_factorization (N : ℕ) (p : CPoly) (hd : p.natDegree ≤ N)
    (h1 : p.eval 1 ≠ 0) (r : Fin p.natDegree → ℂ)
    (hr : Finset.univ.val.map r = p.roots) :
    monicCayleyPolynomial N p =
      (Polynomial.X + 1) ^ (N - p.natDegree) *
        ∏ i : Fin p.natDegree, (Polynomial.X - Polynomial.C ((1 + r i) / (1 - r i))) := by
  classical
  have hri : ∀ i, r i ≠ 1 := by
    intro i hi
    have hroot := isRoot_of_root_enumeration p r hr i
    rw [hi] at hroot
    exact h1 hroot
  have htop := eval_eq_prod_root_enumeration p r hr 1
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_singleton (-1 : ℂ)).infinite_compl.mono
  intro z hz
  -- Membership in the complement of {-1} is precisely the denominator exclusion z ≠ -1.
  change z ≠ (-1 : ℂ) at hz
  have hzden : z + 1 ≠ 0 := by
    intro he
    apply hz
    exact eq_neg_of_add_eq_zero_left he
  -- Expose membership in the set of evaluation-agreement points as the evaluation equality.
  change (monicCayleyPolynomial N p).eval z = _
  simp only [monicCayleyPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_sub]
  rw [cayley_eval N p hd z hzden,
    eval_eq_prod_root_enumeration p r hr ((z - 1) / (z + 1))]
  have hf : ∀ i, (z - 1) / (z + 1) - r i =
      ((1 - r i) / (z + 1)) * (z - (1 + r i) / (1 - r i)) :=
    fun i => cayley_linear_factor z (r i) hzden (hri i)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_sub₀ (z + 1) hzden hd]
  simp only [div_eq_mul_inv]
  calc
    _ = ((p.eval 1)⁻¹ * p.eval 1) * (z + 1) ^ N * ((z + 1) ^ p.natDegree)⁻¹ *
        ∏ i : Fin p.natDegree, (z - (1 + r i) * (1 - r i)⁻¹) := by
      rw [htop]
      ring
    _ = _ := by rw [inv_mul_cancel₀ h1, one_mul]

theorem cayley_degree_and_count (N : ℕ) (p : CPoly)
    (hd : p.natDegree ≤ N) (h1 : p.eval 1 ≠ 0) :
    (monicCayleyPolynomial N p).Monic ∧
    (monicCayleyPolynomial N p).natDegree = N ∧
    diskRootCount p = rightHalfPlaneRootCount (monicCayleyPolynomial N p) := by
  classical
  obtain ⟨r, hr⟩ := exists_roots_enumeration p p.natDegree rfl
  have hm := monicCayley_monic_and_degree N p hd h1
  have hf := monicCayley_factorization N p hd h1 r hr
  have hprodne : ((Polynomial.X + 1) ^ (N - p.natDegree) *
      ∏ i : Fin p.natDegree, (Polynomial.X - Polynomial.C ((1 + r i) / (1 - r i)))) ≠ 0 := by
    rw [← hf]
    exact hm.1.ne_zero
  have hlinear : (Polynomial.X + 1 : CPoly).roots = {(-1 : ℂ)} := by
    simpa only [Polynomial.C_1] using Polynomial.roots_X_add_C (1 : ℂ)
  have hnegative : (((Polynomial.X + 1) ^ (N - p.natDegree) : CPoly).roots.filter
      (fun z : ℂ => 0 < z.re)) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro z hz
    rw [Polynomial.roots_pow, hlinear, Multiset.nsmul_singleton] at hz
    have hz' : z = -1 := Multiset.eq_of_mem_replicate hz
    simp [hz']
  refine ⟨hm.1, hm.2, ?_⟩
  symm
  unfold rightHalfPlaneRootCount diskRootCount
  rw [hf, Polynomial.roots_mul hprodne, Multiset.filter_add, hnegative, zero_add,
    roots_of_prod_root_enumeration, ← hr, Multiset.filter_map, Multiset.card_map,
    Multiset.filter_map, Multiset.card_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro i _
  have hri : r i ≠ 1 := by
    intro hi
    have hroot := isRoot_of_root_enumeration p r hr i
    rw [hi] at hroot
    exact h1 hroot
  exact inverse_cayley_re_pos_iff (r i) hri

#print axioms monicCayley_factorization
#print axioms cayley_degree_and_count

end NLA.MF18

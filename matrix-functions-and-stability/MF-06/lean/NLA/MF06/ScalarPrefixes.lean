/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The actual finite prefix and suffix partition the total. A first prefix
reaching half the positive total overshoots it by at most one summand bound.
The proof uses the least natural index, with no enumeration of the sequence.
-/
import NLA.MF06.GeometricCuts
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06

lemma scalarPrefix_add_suffix {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    scalarPrefix x k + scalarSuffix x k = ∑ i : Fin n, x i := by
  simpa only [scalarPrefix, scalarSuffix, not_lt] using
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < k) x

@[simp] lemma scalarPrefix_zero {n : ℕ} (x : Fin n → ℝ) : scalarPrefix x 0 = 0 := by
  simp [scalarPrefix]

lemma scalarPrefix_total {n : ℕ} (x : Fin n → ℝ) : scalarPrefix x n = ∑ i : Fin n, x i := by
  have hset : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ :=
    Finset.filter_eq_self.mpr (fun i _ => i.isLt)
  unfold scalarPrefix
  rw [hset]

lemma scalarPrefix_succ {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hkn : k < n) :
    scalarPrefix x (k + 1) = scalarPrefix x k + x ⟨k, hkn⟩ := by
  let j : Fin n := ⟨k, hkn⟩
  have hset : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
      insert j (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    change i.val < k + 1 ↔ i.val = k ∨ i.val < k
    omega
  have hj : j ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by simp [j]
  unfold scalarPrefix
  rw [hset, Finset.sum_insert hj]
  exact add_comm _ _

lemma scalar_half_cut {n : ℕ} (x : Fin n → ℝ) (K : ℝ)
    (hxK : ∀ i, x i ≤ K) (hpositive : 0 < ∑ i : Fin n, x i) :
    ∃ k : ℕ, k ≤ n ∧
      (∑ i : Fin n, x i) / 2 ≤ scalarPrefix x k ∧
      scalarPrefix x k ≤ (∑ i : Fin n, x i) / 2 + K := by
  classical
  let X := ∑ i : Fin n, x i
  have hX : 0 < X := hpositive
  have htotal : X / 2 ≤ scalarPrefix x n := by
    rw [scalarPrefix_total]
    change X / 2 ≤ X
    linarith
  have hex : ∃ k : ℕ, X / 2 ≤ scalarPrefix x k := ⟨n, htotal⟩
  let k := Nat.find hex
  have hhalf : X / 2 ≤ scalarPrefix x k := Nat.find_spec hex
  have hkn : k ≤ n := Nat.find_min' hex htotal
  have hkpos : 0 < k := by
    by_contra h
    have hkzero : k = 0 := by omega
    rw [hkzero, scalarPrefix_zero] at hhalf
    linarith
  have hprev : scalarPrefix x (k - 1) < X / 2 := by
    apply lt_of_not_ge
    exact Nat.find_min hex (by change k - 1 < k; omega)
  have hprevn : k - 1 < n := by omega
  have hstep := scalarPrefix_succ x (k - 1) hprevn
  have hindex : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  rw [hindex] at hstep
  refine ⟨k, hkn, hhalf, ?_⟩
  have hlast := hxK ⟨k - 1, hprevn⟩
  linarith

#print axioms scalar_half_cut
#assert_trust kernel scalar_half_cut

end NLA.MF06

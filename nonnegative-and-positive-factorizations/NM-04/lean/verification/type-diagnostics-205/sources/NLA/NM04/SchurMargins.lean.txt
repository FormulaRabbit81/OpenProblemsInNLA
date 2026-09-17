/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The three actual Schur-tail margins, including one-row and one-column matrices.
-/
import NLA.NM04.Definitions
import LeanCert.Tactic
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
open scoped BigOperators

/-- Summing the actual tail labels removes only the distinguished first label. -/
theorem sum_tail {n : ℕ} (hn : 1 ≤ n) (f : Fin n → ℝ) :
    (∑ i : Tail n, f i.val) = (∑ i : Fin n, f i) - f (firstIndex hn) := by
  rw [← Finset.sum_erase_eq_sub (Finset.mem_univ (firstIndex hn))]
  symm
  apply Finset.sum_subtype
  intro i
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro h
    by_contra hi
    apply h
    apply Fin.ext
    change i.val = 0
    omega
  · intro hi heq
    have : i.val = 0 := congrArg Fin.val heq
    omega

theorem schur_margin_identities {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (hS : Positive S) (hB : Balanced S) :
    (∀ i : Tail m, (∑ j : Tail n, schurTail S hm hn i j) =
      1 - S i.val (firstIndex hn) / S (firstIndex hm) (firstIndex hn)) ∧
    (∀ j : Tail n, (∑ i : Tail m, schurTail S hm hn i j) =
      ((m : ℝ) / (n : ℝ)) *
        (1 - S (firstIndex hm) j.val / S (firstIndex hm) (firstIndex hn))) ∧
    (∑ i : Tail m, ∑ j : Tail n, schurTail S hm hn i j) =
      (m : ℝ) - ((m : ℝ) / (n : ℝ)) / S (firstIndex hm) (firstIndex hn) := by
  have hx : S (firstIndex hm) (firstIndex hn) ≠ 0 :=
    ne_of_gt (hS (firstIndex hm) (firstIndex hn))
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hrow (i : Tail m) : (∑ j : Tail n, schurTail S hm hn i j) =
      1 - S i.val (firstIndex hn) / S (firstIndex hm) (firstIndex hn) := by
    simp_rw [schurTail, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    rw [sum_tail hn, sum_tail hn, hB.1, hB.1]
    field_simp [hx]
    ring
  refine ⟨hrow, ?_, ?_⟩
  · intro j
    simp_rw [schurTail, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    rw [sum_tail hm (fun i => S i j.val),
      sum_tail hm (fun i => S i (firstIndex hn)), hB.2, hB.2]
    field_simp [hx, hn0]
    ring
  · calc
      (∑ i : Tail m, ∑ j : Tail n, schurTail S hm hn i j) =
          ∑ i : Tail m,
            (1 - S i.val (firstIndex hn) / S (firstIndex hm) (firstIndex hn)) :=
        Finset.sum_congr rfl (fun i _ => hrow i)
      _ = (m : ℝ) - ((m : ℝ) / (n : ℝ)) /
          S (firstIndex hm) (firstIndex hn) := by
        rw [sum_tail hm (fun i =>
          1 - S i (firstIndex hn) / S (firstIndex hm) (firstIndex hn))]
        simp [Finset.sum_sub_distrib, ← Finset.sum_div, hB.2, div_self hx]

#print axioms schur_margin_identities
#assert_trust kernel schur_margin_identities

end NLA.NM04

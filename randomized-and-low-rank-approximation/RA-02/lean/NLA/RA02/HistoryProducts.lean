/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Literal chronological products and their bridge to the conditional path law.
The probability identity requires and retains every nonzero prefix trace.
-/
import NLA.RA02.PathSemantics
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

@[simp] lemma pivotProduct_nil {n : ℕ} (A : Square n) : pivotProduct A [] = 1 := by
  simp [pivotProduct]

@[simp] lemma prefixTraceProduct_nil {n : ℕ} (A : Square n) : prefixTraceProduct A [] = 1 := by
  simp [prefixTraceProduct]

lemma pivotProduct_cons {n : ℕ} (A : Square n) (j : Fin n) (w : List (Fin n)) :
    pivotProduct A (j :: w) = (A j j).re * pivotProduct (choleskyStep A j) w := by
  let f : Fin (w.length + 1) → ℝ := fun s =>
    ((pathResidual A ((j :: w).take s.val)) ((j :: w).get s) ((j :: w).get s)).re
  change (∏ s : Fin (w.length + 1), f s) = f 0 * ∏ s : Fin w.length, f s.succ
  exact Fin.prod_univ_succ f

lemma prefixTraceProduct_cons {n : ℕ} (A : Square n) (j : Fin n) (w : List (Fin n)) :
    prefixTraceProduct A (j :: w) = realTrace A * prefixTraceProduct (choleskyStep A j) w := by
  let f : Fin (w.length + 1) → ℝ := fun s =>
    realTrace (pathResidual A ((j :: w).take s.val))
  change (∏ s : Fin (w.length + 1), f s) = f 0 * ∏ s : Fin w.length, f s.succ
  exact Fin.prod_univ_succ f

lemma pivotProduct_append_singleton {n : ℕ} (A : Square n)
    (w : List (Fin n)) (j : Fin n) :
    pivotProduct A (w ++ [j]) =
      pivotProduct A w * ((pathResidual A w) j j).re := by
  induction w generalizing A with
  | nil => simp [pivotProduct_cons, pathResidual]
  | cons k w ih =>
      simpa only [List.cons_append, pivotProduct_cons, pathResidual, mul_assoc] using
        congrArg (fun t : ℝ => (A k k).re * t) (ih (choleskyStep A k))

lemma pathWeight_eq_pivotProduct_div {n : ℕ} (A : Square n) (w : List (Fin n))
    (htrace : ∀ s : Fin w.length, realTrace (pathResidual A (w.take s.val)) ≠ 0) :
    pathWeight A w = pivotProduct A w / prefixTraceProduct A w := by
  induction w generalizing A with
  | nil => simp [pathWeight]
  | cons j w ih =>
      have hfirst : realTrace A ≠ 0 := by
        simpa only [Fin.val_zero, List.take_zero, pathResidual] using
          htrace (0 : Fin (j :: w).length)
      have htail : ∀ s : Fin w.length,
          realTrace (pathResidual (choleskyStep A j) (w.take s.val)) ≠ 0 := by
        intro s
        simpa only [Fin.val_succ, List.take_succ_cons, pathResidual] using htrace s.succ
      rw [pathWeight, pivotMass, if_neg hfirst, ih (choleskyStep A j) htail,
        pivotProduct_cons, prefixTraceProduct_cons]
      exact div_mul_div_comm _ _ _ _

#print axioms pivotProduct_cons
#assert_trust kernel pivotProduct_cons
#print axioms pathWeight_eq_pivotProduct_div
#assert_trust kernel pathWeight_eq_pivotProduct_div

end
end NLA.RA02

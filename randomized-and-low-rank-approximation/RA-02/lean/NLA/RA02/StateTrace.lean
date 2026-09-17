/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Full zero-padded state traces, not active-submatrix surrogates. Equality with
the auxiliary potential is proved only when exactly one label remains.
-/
import NLA.RA02.StatePotential
import NLA.RA02.HistoryCardinality

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma state_true_trace (r : ℕ) (U : Finset (Fin r)) :
    realTrace (arrowheadState r U true) = cornerValue r U + ∑ i ∈ U, diagonalWeight r i.val := by
  rw [realTrace_eq_sum, Fin.sum_univ_castSucc, state_true_last_last, Complex.ofReal_re]
  have hsum : (∑ i ∈ U, (arrowheadState r U true i.castSucc i.castSucc).re) =
      ∑ i : Fin r, (arrowheadState r U true i.castSucc i.castSucc).re := by
    apply Finset.sum_subset (Finset.subset_univ U)
    intro i _ hi
    simp [hi]
  rw [← hsum]
  have hdiag : (∑ i ∈ U, (arrowheadState r U true i.castSucc i.castSucc).re) =
      ∑ i ∈ U, diagonalWeight r i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    exact state_true_diagonal r U i hi
  rw [hdiag, add_comm]

lemma state_false_trace (r : ℕ) (U : Finset (Fin r)) :
    realTrace (arrowheadState r U false) =
      ∑ i ∈ U, diagonalWeight r i.val * cornerValue r (U.erase i) / cornerValue r U := by
  rw [realTrace_eq_sum, Fin.sum_univ_castSucc, state_false_last_last, Complex.zero_re, add_zero]
  have hsum : (∑ i ∈ U, (arrowheadState r U false i.castSucc i.castSucc).re) =
      ∑ i : Fin r, (arrowheadState r U false i.castSucc i.castSucc).re := by
    apply Finset.sum_subset (Finset.subset_univ U)
    intro i _ hi
    simp [hi]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact state_false_diagonal r U i hi

lemma state_trace_eq_potential_when_one (r : ℕ) (U : Finset (Fin r)) (b : Bool)
    (hcard : U.card + (if b then 1 else 0) = 1) :
    realTrace (arrowheadState r U b) = statePotential r U b := by
  cases b
  · have hU : U.card = 1 := by simpa using hcard
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hU
    rw [state_false_trace]
    simp only [Finset.sum_singleton, Finset.erase_singleton, statePotential,
      Bool.false_eq_true, ↓reduceIte, Finset.prod_singleton]
    have hempty : cornerValue r ∅ = scaleParameter r ^ r := by
      simp [cornerValue]
    rw [hempty]
    ring
  · have hU : U.card = 0 := by simpa using hcard
    have hUempty : U = ∅ := Finset.card_eq_zero.mp hU
    subst U
    simp [state_true_trace, statePotential, cornerValue]

#print axioms state_true_trace
#assert_trust kernel state_true_trace
#print axioms state_false_trace
#assert_trust kernel state_false_trace
#print axioms state_trace_eq_potential_when_one
#assert_trust kernel state_trace_eq_potential_when_one

end
end NLA.RA02

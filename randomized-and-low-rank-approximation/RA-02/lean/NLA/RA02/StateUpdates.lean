/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Both frozen residual shapes evolve under the actual complex Cholesky step.
The false-state update follows by commuting genuine nonzero pivots.
-/
import NLA.RA02.StateConstruction
import NLA.RA02.PivotCommutation

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma state_active_pivot_ne_zero (r : ℕ) (U : Finset (Fin r)) (b : Bool)
    (i : Fin r) (hi : i ∈ U) : arrowheadState r U b i.castSucc i.castSucc ≠ 0 := by
  have hre : 0 < (arrowheadState r U b i.castSucc i.castSucc).re := by
    cases b
    · rw [state_false_diagonal r U i hi]
      exact div_pos (mul_pos (diagonalWeight_pos r i.val)
        (cornerValue_pos r (U.erase i))) (cornerValue_pos r U)
    · rw [state_true_diagonal r U i hi]
      exact diagonalWeight_pos r i.val
  intro hz
  exact (ne_of_gt hre) (congrArg Complex.re hz)

lemma state_true_ordinary_pivot (r : ℕ) (U : Finset (Fin r))
    (i : Fin r) (hi : i ∈ U) :
    choleskyStep (arrowheadState r U true) i.castSucc =
      arrowheadState r (U.erase i) true := by
  have hpivot := state_active_pivot_ne_zero r U true i hi
  have hstep (x y : Fin (r + 1)) :
      choleskyStep (arrowheadState r U true) i.castSucc x y =
        arrowheadState r U true x y -
          arrowheadState r U true x i.castSucc *
            arrowheadState r U true i.castSucc y /
              arrowheadState r U true i.castSucc i.castSucc := by
    simp only [choleskyStep, hpivot, ↓reduceIte]
  have hcorner : cornerValue r U -
      (diagonalWeight r i.val * couplingWeight r i.val) *
        (diagonalWeight r i.val * couplingWeight r i.val) / diagonalWeight r i.val =
          cornerValue r (U.erase i) := by
    rw [cornerValue_erase r U i hi]
    field_simp [(diagonalWeight_pos r i.val).ne'] <;> ring
  ext x y
  refine Fin.lastCases ?_ (fun x => ?_) x
  · refine Fin.lastCases ?_ (fun y => ?_) y
    · rw [hstep]
      simp only [state_true_last_last, state_true_last_ordinary,
        state_true_ordinary_last, state_true_ordinary, hi, ↓reduceIte]
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div] using
        congrArg (fun t : ℝ => (t : ℂ)) hcorner
    · by_cases hy : y = i
      · subst y
        simpa using choleskyStep_pivot_col (arrowheadState r U true)
          i.castSucc hpivot (Fin.last r)
      · rw [hstep]
        simp [hy, Ne.symm hy, Finset.mem_erase]
  · refine Fin.lastCases ?_ (fun y => ?_) y
    · by_cases hx : x = i
      · subst x
        simpa using choleskyStep_pivot_row (arrowheadState r U true)
          i.castSucc hpivot (Fin.last r)
      · rw [hstep]
        simp [hx, Ne.symm hx, Finset.mem_erase]
    · by_cases hx : x = i
      · subst x
        simpa using choleskyStep_pivot_row (arrowheadState r U true)
          i.castSucc hpivot y.castSucc
      · by_cases hy : y = i
        · subst y
          simpa [hx] using choleskyStep_pivot_col (arrowheadState r U true)
            i.castSucc hpivot x.castSucc
        · rw [hstep]
          simp [hx, Ne.symm hx, hy, Ne.symm hy, Finset.mem_erase]

lemma state_false_ordinary_pivot (r : ℕ) (U : Finset (Fin r))
    (i : Fin r) (hi : i ∈ U) :
    choleskyStep (arrowheadState r U false) i.castSucc =
      arrowheadState r (U.erase i) false := by
  have hlast : arrowheadState r U true (Fin.last r) (Fin.last r) ≠ 0 := by
    rw [state_true_last_last]
    exact_mod_cast (cornerValue_pos r U).ne'
  have hordinary := state_active_pivot_ne_zero r U true i hi
  have hlast_ordinary :
      choleskyStep (arrowheadState r U true) (Fin.last r) i.castSucc i.castSucc ≠ 0 := by
    rw [state_true_last_pivot]
    exact state_active_pivot_ne_zero r U false i hi
  have hordinary_last :
      choleskyStep (arrowheadState r U true) i.castSucc (Fin.last r) (Fin.last r) ≠ 0 := by
    rw [state_true_ordinary_pivot r U i hi, state_true_last_last]
    exact_mod_cast (cornerValue_pos r (U.erase i)).ne'
  calc
    choleskyStep (arrowheadState r U false) i.castSucc =
        choleskyStep (choleskyStep (arrowheadState r U true) (Fin.last r)) i.castSucc := by
      rw [state_true_last_pivot]
    _ = choleskyStep (choleskyStep (arrowheadState r U true) i.castSucc) (Fin.last r) :=
      choleskyStep_commute (arrowheadState r U true) (Fin.last r) i.castSucc
        hlast hordinary hlast_ordinary hordinary_last
    _ = arrowheadState r (U.erase i) false := by
      rw [state_true_ordinary_pivot r U i hi, state_true_last_pivot]

theorem residual_state_updates (r : ℕ) (hr : 1 ≤ r) (U : Finset (Fin r)) :
    choleskyStep (arrowheadState r U true) (Fin.last r) = arrowheadState r U false ∧
    ∀ i ∈ U,
      choleskyStep (arrowheadState r U true) i.castSucc = arrowheadState r (U.erase i) true ∧
      choleskyStep (arrowheadState r U false) i.castSucc = arrowheadState r (U.erase i) false := by
  refine ⟨state_true_last_pivot r U, ?_⟩
  intro i hi
  exact ⟨state_true_ordinary_pivot r U i hi, state_false_ordinary_pivot r U i hi⟩

#print axioms state_true_ordinary_pivot
#assert_trust kernel state_true_ordinary_pivot
#print axioms state_false_ordinary_pivot
#assert_trust kernel state_false_ordinary_pivot
#print axioms residual_state_updates
#assert_trust kernel residual_state_updates

end
end NLA.RA02

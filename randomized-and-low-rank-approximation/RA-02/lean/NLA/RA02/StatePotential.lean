/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

An explicit auxiliary multiplicative potential, not a new trace definition.
The empty false state's potential is one although its residual trace is zero.
-/
import NLA.RA02.HistoryProducts
import NLA.RA02.DistinctHistory

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

def statePotential (r : ℕ) (U : Finset (Fin r)) (lastPresent : Bool) : ℝ :=
  if lastPresent then scaleParameter r ^ r * ∏ i ∈ U, diagonalWeight r i.val
  else (scaleParameter r ^ r * ∏ i ∈ U, diagonalWeight r i.val) / cornerValue r U

lemma statePotential_pos (r : ℕ) (U : Finset (Fin r)) (b : Bool) :
    0 < statePotential r U b := by
  have hnum : 0 < scaleParameter r ^ r * ∏ i ∈ U, diagonalWeight r i.val :=
    mul_pos (pow_pos (scaleParameter_pos r) r)
      (Finset.prod_pos (fun i _ => diagonalWeight_pos r i.val))
  cases b
  · exact div_pos hnum (cornerValue_pos r U)
  · exact hnum

lemma statePotential_initial (r : ℕ) :
    statePotential r Finset.univ true = commonNumerator r := by
  rfl

lemma statePotential_true_ordinary (r : ℕ) (U : Finset (Fin r))
    (i : Fin r) (hi : i ∈ U) :
    diagonalWeight r i.val * statePotential r (U.erase i) true = statePotential r U true := by
  change diagonalWeight r i.val *
      (scaleParameter r ^ r * ∏ j ∈ U.erase i, diagonalWeight r j.val) =
    scaleParameter r ^ r * ∏ j ∈ U, diagonalWeight r j.val
  calc
    diagonalWeight r i.val * (scaleParameter r ^ r *
        ∏ j ∈ U.erase i, diagonalWeight r j.val) =
        scaleParameter r ^ r * (diagonalWeight r i.val *
          ∏ j ∈ U.erase i, diagonalWeight r j.val) := by ring
    _ = scaleParameter r ^ r * ∏ j ∈ U, diagonalWeight r j.val :=
      congrArg (fun t : ℝ => scaleParameter r ^ r * t)
        (Finset.mul_prod_erase U (fun j : Fin r => diagonalWeight r j.val) hi)

lemma statePotential_false_ordinary (r : ℕ) (U : Finset (Fin r))
    (i : Fin r) (hi : i ∈ U) :
    (diagonalWeight r i.val * cornerValue r (U.erase i) / cornerValue r U) *
      statePotential r (U.erase i) false = statePotential r U false := by
  have htrue := statePotential_true_ordinary r U i hi
  change diagonalWeight r i.val * cornerValue r (U.erase i) / cornerValue r U *
      ((scaleParameter r ^ r * ∏ j ∈ U.erase i, diagonalWeight r j.val) /
        cornerValue r (U.erase i)) =
    (scaleParameter r ^ r * ∏ j ∈ U, diagonalWeight r j.val) / cornerValue r U
  calc
    diagonalWeight r i.val * cornerValue r (U.erase i) / cornerValue r U *
        ((scaleParameter r ^ r * ∏ j ∈ U.erase i, diagonalWeight r j.val) /
          cornerValue r (U.erase i)) =
        (diagonalWeight r i.val *
          (scaleParameter r ^ r * ∏ j ∈ U.erase i, diagonalWeight r j.val)) /
            cornerValue r U := by
      field_simp [(cornerValue_pos r U).ne', (cornerValue_pos r (U.erase i)).ne'] <;> ring
    _ = (scaleParameter r ^ r * ∏ j ∈ U, diagonalWeight r j.val) / cornerValue r U :=
      congrArg (fun t : ℝ => t / cornerValue r U) htrue

lemma statePotential_ordinary (r : ℕ) (U : Finset (Fin r)) (b : Bool)
    (i : Fin r) (hi : i ∈ U) :
    (arrowheadState r U b i.castSucc i.castSucc).re * statePotential r (U.erase i) b =
      statePotential r U b := by
  cases b
  · rw [state_false_diagonal r U i hi]
    exact statePotential_false_ordinary r U i hi
  · rw [state_true_diagonal r U i hi]
    exact statePotential_true_ordinary r U i hi

lemma statePotential_last (r : ℕ) (U : Finset (Fin r)) :
    cornerValue r U * statePotential r U false = statePotential r U true := by
  exact mul_div_cancel₀ _ (cornerValue_pos r U).ne'

lemma pivotProduct_statePotential (r : ℕ) (w : List (Fin (r + 1))) (hw : w.Nodup) :
    pivotProduct (arrowhead r) w *
      statePotential r (remainingOrdinary r w) (lastRemaining r w) = commonNumerator r := by
  revert hw
  induction w using List.reverseRecOn with
  | nil =>
      intro _
      simp [statePotential_initial]
  | append_singleton w j ih =>
      intro hw
      have hw' : w.Nodup := (List.nodup_append.mp hw).1
      have hj : j ∉ w := by
        intro hjw
        exact (List.nodup_append.mp hw).2.2 j hjw j (by simp) rfl
      rw [pivotProduct_append_singleton, pathResidual_distinct_state r w hw']
      revert hj
      refine Fin.lastCases ?_ (fun i => ?_) j
      · intro hlast
        rw [remainingOrdinary_append_last, lastRemaining_append_last,
          lastRemaining_of_not_mem r w hlast, state_true_last_last, Complex.ofReal_re,
          mul_assoc, statePotential_last]
        simpa only [lastRemaining_of_not_mem r w hlast] using ih hw'
      · intro hi
        have hiU : i ∈ remainingOrdinary r w := (mem_remainingOrdinary r w i).2 hi
        rw [remainingOrdinary_append_ordinary, lastRemaining_append_ordinary,
          mul_assoc, statePotential_ordinary r (remainingOrdinary r w) (lastRemaining r w) i hiU]
        exact ih hw'

#print axioms statePotential_ordinary
#assert_trust kernel statePotential_ordinary
#print axioms pivotProduct_statePotential
#assert_trust kernel pivotProduct_statePotential

end
end NLA.RA02

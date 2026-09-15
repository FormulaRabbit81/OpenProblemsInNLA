/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Scalar
import NLA.SP04.MatrixStationary

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

theorem diagonal_difference_frobeniusSq {n : ℕ} (s x : Fin n → ℝ) :
    frobeniusSq (Matrix.diagonal s - Matrix.diagonal x) = ∑ i, (s i-x i)^2 := by
  rw [Matrix.diagonal_sub]
  simp [frobeniusSq, Matrix.diagonal_apply]

theorem selected_unique_least (s : Fin 3 → ℝ) (hs : Admissible s)
    (t : ℝ) (ht : 0<t) (hT : t<13/25) (hg : selectedProduct s t=1) :
    UniqueLeastStationary (Matrix.diagonal s) (selectedMatrix s t) (-t) := by
  have hsel := selected_scalar_stationary s hs t ht hg
  constructor
  · exact (all_diagonal_stationary_iff s hs (selectedMatrix s t) (-t)).mpr
      ⟨selectedEntries s t, rfl, hsel.1, hsel.2⟩
  · intro Y c hY
    obtain ⟨x, hYx, hxq, hxp⟩ := (all_diagonal_stationary_iff s hs Y c).mp hY
    have h := scalar_least_unique s hs t ht hT hg x c ⟨hxq,hxp⟩
    rw [abs_neg, abs_of_pos ht]
    refine ⟨h.1, fun he => ?_⟩
    obtain ⟨hxe, hce⟩ := h.2 he
    exact ⟨by simpa [selectedMatrix, hxe] using hYx, hce⟩

theorem diagonal_counterexample_full (s : Fin 3 → ℝ) (hs : Admissible s) :
    ∃ t : ℝ, 0 < t ∧ t < 13/25 ∧
      UniqueLeastStationary (Matrix.diagonal s) (selectedMatrix s t) (-t) ∧
      Feasible (improvedMatrix s t) ∧
      frobeniusNorm (Matrix.diagonal s - improvedMatrix s t) <
        frobeniusNorm (Matrix.diagonal s - selectedMatrix s t) := by
  obtain ⟨t, ht, hT, hg⟩ := selected_parameter_exists s hs
  refine ⟨t, ht, hT, selected_unique_least s hs t ht hT hg, ?_, ?_⟩
  · simpa [Feasible, improvedMatrix, Matrix.det_diagonal] using
      improved_scalar_feasible s hs t ht hg
  · simp only [frobeniusNorm, improvedMatrix, selectedMatrix, diagonal_difference_frobeniusSq]
    exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      (scalar_distance_improves s hs t ht)

#assert_trust kernel selected_unique_least
#assert_trust kernel diagonal_counterexample_full
#print axioms selected_unique_least
#print axioms diagonal_counterexample_full

end NLA.SP04

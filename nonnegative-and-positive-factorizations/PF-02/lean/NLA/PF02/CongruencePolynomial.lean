/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.PF02.Coordinates

noncomputable section
open Matrix
namespace NLA.PF02

set_option maxHeartbeats 1600000 in
/-- The determinant of the actual symmetric congruence representation, for every real matrix. -/
theorem congruenceCoordinates_det (S : Mat 3 3) :
    (congruenceCoordinates S).det = S.det ^ 4 := by
  rw [Matrix.det_fin_three S]
  unfold congruenceCoordinates
  eval_det
  ring

/-- The coordinate determinant transforms by a positive fourth power for every invertible S. -/
theorem orientation_congruent (F G : Factorization witnessM 3) (h : Congruent F G) :
    (0 < orientationDet F ↔ 0 < orientationDet G) := by
  obtain ⟨S, hS, _⟩ := h
  have hrow : rowCoordinates G.val.1 = rowCoordinates F.val.1 * congruenceCoordinates S := by
    rw [show G.val.1 = (fun i => (↑S : Mat 3 3).transpose * F.val.1 i * ↑S) from funext hS]
    exact rowCoordinates_congruence S F.val.1 (fun i => (F.property.1 i).isHermitian)
  have hdet : orientationDet G = orientationDet F * (↑S : Mat 3 3).det ^ 4 := by
    unfold orientationDet
    rw [hrow, Matrix.det_mul, congruenceCoordinates_det]
  have hnonzero : (↑S : Mat 3 3).det ≠ 0 := (Matrix.isUnits_det_units S).ne_zero
  have hpos : 0 < (↑S : Mat 3 3).det ^ 4 := by positivity
  rw [hdet, mul_pos_iff_of_pos_right hpos]

#assert_trust kernel congruenceCoordinates_det
#assert_trust kernel orientation_congruent
#print axioms congruenceCoordinates_det
#print axioms orientation_congruent

end NLA.PF02

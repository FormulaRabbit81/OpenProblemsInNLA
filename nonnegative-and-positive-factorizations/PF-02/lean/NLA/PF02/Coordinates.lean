/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.PF02.Data

noncomputable section
open Matrix
namespace NLA.PF02

/-- The actual trace pairing in diagonal/upper-triangle coordinates. -/
def traceMetric : Mat 6 6 := Matrix.diagonal ![1,1,1,2,2,2]

/-- Trace-coordinate identity for every pair of real symmetric matrices. -/
theorem trace_coordinate_identity (X Y : Mat 3 3)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Matrix.trace (X * Y) = (coord X ᵥ* traceMetric) ⬝ᵥ coord Y := by
  have hx10 : X 1 0 = X 0 1 := by simpa using hX.apply 0 1
  have hx20 : X 2 0 = X 0 2 := by simpa using hX.apply 0 2
  have hx21 : X 2 1 = X 1 2 := by simpa using hX.apply 1 2
  have hy10 : Y 1 0 = Y 0 1 := by simpa using hY.apply 0 1
  have hy20 : Y 2 0 = Y 0 2 := by simpa using hY.apply 0 2
  have hy21 : Y 2 1 = Y 1 2 := by simpa using hY.apply 1 2
  simp [Matrix.trace, Matrix.mul_apply, coord, traceMetric, vecMul, dotProduct,
    Fin.sum_univ_succ, hx10, hx20, hx21, hy10, hy20, hy21]
  ring

/-- The complete trace constraints yield a matrix factorization on the entire PSD fiber. -/
theorem factorization_coordinate_identity (F : Factorization witnessM 3) :
    witnessM = rowCoordinates F.val.1 * traceMetric * (rowCoordinates F.val.2).transpose := by
  ext i j
  rw [← F.property.2.2 i j,
    trace_coordinate_identity _ _ (F.property.1 i).isHermitian
      (F.property.2.1 j).isHermitian]
  rfl

/-- Coordinates of the actual congruence action on symmetric three-by-three matrices. -/
def congruenceCoordinates (S : Mat 3 3) : Mat 6 6 := !![
  (S 0 0)^2, (S 0 1)^2, (S 0 2)^2, S 0 0*S 0 1, S 0 0*S 0 2, S 0 1*S 0 2;
  (S 1 0)^2, (S 1 1)^2, (S 1 2)^2, S 1 0*S 1 1, S 1 0*S 1 2, S 1 1*S 1 2;
  (S 2 0)^2, (S 2 1)^2, (S 2 2)^2, S 2 0*S 2 1, S 2 0*S 2 2, S 2 1*S 2 2;
  2*S 0 0*S 1 0, 2*S 0 1*S 1 1, 2*S 0 2*S 1 2,
    S 0 0*S 1 1+S 0 1*S 1 0, S 0 0*S 1 2+S 0 2*S 1 0, S 0 1*S 1 2+S 0 2*S 1 1;
  2*S 0 0*S 2 0, 2*S 0 1*S 2 1, 2*S 0 2*S 2 2,
    S 0 0*S 2 1+S 0 1*S 2 0, S 0 0*S 2 2+S 0 2*S 2 0, S 0 1*S 2 2+S 0 2*S 2 1;
  2*S 1 0*S 2 0, 2*S 1 1*S 2 1, 2*S 1 2*S 2 2,
    S 1 0*S 2 1+S 1 1*S 2 0, S 1 0*S 2 2+S 1 2*S 2 0, S 1 1*S 2 2+S 1 2*S 2 1]

/-- Every coordinate of the actual congruence is represented, for all real entries. -/
theorem congruence_covariance (S X : Mat 3 3) (hX : X.IsHermitian) :
    coord (S.transpose * X * S) = coord X ᵥ* congruenceCoordinates S := by
  have hx10 : X 1 0 = X 0 1 := by simpa using hX.apply 0 1
  have hx20 : X 2 0 = X 0 2 := by simpa using hX.apply 0 2
  have hx21 : X 2 1 = X 1 2 := by simpa using hX.apply 1 2
  ext j
  fin_cases j <;>
    simp [coord, congruenceCoordinates, Matrix.mul_apply, vecMul, dotProduct,
      Fin.sum_univ_succ, hx10, hx20, hx21] <;> ring

/-- The coordinate transformation applies simultaneously to every member of a real family. -/
theorem rowCoordinates_congruence (S : Mat 3 3) (A : Fin 6 → Mat 3 3)
    (hA : ∀ i, (A i).IsHermitian) :
    rowCoordinates (fun i => S.transpose * A i * S) =
      rowCoordinates A * congruenceCoordinates S := by
  ext i j
  exact congrFun (congruence_covariance S (A i) (hA i)) j

#assert_trust kernel trace_coordinate_identity
#assert_trust kernel factorization_coordinate_identity
#assert_trust kernel congruence_covariance
#assert_trust kernel rowCoordinates_congruence
#print axioms trace_coordinate_identity
#print axioms factorization_coordinate_identity
#print axioms congruence_covariance
#print axioms rowCoordinates_congruence

end NLA.PF02

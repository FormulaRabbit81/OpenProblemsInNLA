/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Diagonal
import NLA.SP04.Finiteness
import NLA.SP04.Orthogonal
import NLA.SP04.MatrixStationary

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

theorem orthogonal_forward_inverse {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (Y : Mat n) :
    P * (Pᵀ * Y * Q) * Qᵀ = Y := by
  simpa only [Matrix.transpose_transpose] using
    orthogonal_inverse_transport (orthogonal_transpose hP) (orthogonal_transpose hQ) Y

/-- Orthogonal transport compares the selected pair with every stationary matrix. -/
theorem uniqueLeastStationary_orthogonal_forward {n : ℕ} {P Q U X : Mat n} {c : ℝ}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (h : UniqueLeastStationary U X c) :
    UniqueLeastStationary (P * U * Qᵀ) (P * X * Qᵀ) c := by
  refine ⟨stationary_orthogonal_forward hP hQ h.1, ?_⟩
  intro Y d hY
  have hback := stationary_orthogonal_forward (orthogonal_transpose hP) (orthogonal_transpose hQ) hY
  simp only [Matrix.transpose_transpose, orthogonal_inverse_transport hP hQ] at hback
  have hcmp := h.2 (Pᵀ * Y * Q) d hback
  refine ⟨hcmp.1, fun he => ?_⟩
  obtain ⟨hYX, hdc⟩ := hcmp.2 he
  have hYeq := congrArg (fun Z : Mat n => P * Z * Qᵀ) hYX
  rw [orthogonal_forward_inverse hP hQ] at hYeq
  exact ⟨hYeq, hdc⟩

theorem uniqueLeastStationary_orthogonal_iff {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (U X : Mat n) (c : ℝ) :
    UniqueLeastStationary (P * U * Qᵀ) (P * X * Qᵀ) c ↔
      UniqueLeastStationary U X c := by
  constructor
  · intro h
    have hh := uniqueLeastStationary_orthogonal_forward (orthogonal_transpose hP)
      (orthogonal_transpose hQ) h
    simpa only [Matrix.transpose_transpose, orthogonal_inverse_transport hP hQ] using hh
  · exact uniqueLeastStationary_orthogonal_forward hP hQ

/-- The whole stationary pair set is the image of the whole original set. -/
theorem stationaryPairs_orthogonal_eq {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (U : Mat n) :
    stationaryPairs (P * U * Qᵀ) =
      (fun p : Mat n × ℝ => (P * p.1 * Qᵀ, p.2)) '' stationaryPairs U := by
  ext p
  constructor
  · intro hp
    have hback := stationary_orthogonal_forward (orthogonal_transpose hP) (orthogonal_transpose hQ) hp
    simp only [Matrix.transpose_transpose, orthogonal_inverse_transport hP hQ] at hback
    refine ⟨(Pᵀ * p.1 * Q, p.2), hback, ?_⟩
    exact Prod.ext (orthogonal_forward_inverse hP hQ p.1) rfl
  · rintro ⟨q, hq, rfl⟩
    exact stationary_orthogonal_forward hP hQ hq

theorem stationaryPairs_finite_orthogonal {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (U : Mat n)
    (hfinite : (stationaryPairs U).Finite) :
    (stationaryPairs (P * U * Qᵀ)).Finite := by
  rw [stationaryPairs_orthogonal_eq hP hQ]
  exact hfinite.image _

theorem stationaryPairs_finite_orthogonal_iff {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (U : Mat n) :
    (stationaryPairs (P * U * Qᵀ)).Finite ↔ (stationaryPairs U).Finite := by
  constructor
  · intro h
    have hh := stationaryPairs_finite_orthogonal (orthogonal_transpose hP)
      (orthogonal_transpose hQ) (P * U * Qᵀ) h
    simpa only [Matrix.transpose_transpose, orthogonal_inverse_transport hP hQ] using hh
  · exact stationaryPairs_finite_orthogonal hP hQ U

/-- A genuine admissible SVD transports the complete diagonal counterexample. -/
theorem selectionFails_of_admissible_svd (U : Mat 3) (s : Fin 3 → ℝ)
    (hs : Admissible s) (hsvd : HasSVD U s) (hregular : RegularData U) : SelectionFails U := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hsvd
  obtain ⟨t, ht, hT, hleast, hfeasible, himproves⟩ := diagonal_counterexample_full s hs
  refine ⟨hregular, stationaryPairs_finite_orthogonal hP hQ (Matrix.diagonal s)
      (diagonal_stationary_finite s hs), P * selectedMatrix s t * Qᵀ, -t,
      uniqueLeastStationary_orthogonal_forward hP hQ hleast,
      P * improvedMatrix s t * Qᵀ, (feasible_orthogonal_iff hP hQ _).mpr hfeasible, ?_⟩
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub,
    frobeniusNorm_orthogonal hP hQ, frobeniusNorm_orthogonal hP hQ]
  exact himproves

#assert_trust kernel uniqueLeastStationary_orthogonal_iff
#assert_trust kernel stationaryPairs_orthogonal_eq
#assert_trust kernel stationaryPairs_finite_orthogonal_iff
#assert_trust kernel selectionFails_of_admissible_svd
#print axioms uniqueLeastStationary_orthogonal_iff
#print axioms stationaryPairs_orthogonal_eq
#print axioms stationaryPairs_finite_orthogonal_iff
#print axioms selectionFails_of_admissible_svd

end NLA.SP04

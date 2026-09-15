/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.SVD

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

lemma svd_gram (P Q : Mat 3) (s : Fin 3 → ℝ) (hP : Orthogonal P) :
    (P * Matrix.diagonal s * Qᵀ)ᵀ * (P * Matrix.diagonal s * Qᵀ) =
      Q * Matrix.diagonal (fun i => (s i)^2) * Qᵀ := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc, orthogonal_cancel_left hP]
  rw [← Matrix.mul_assoc (Matrix.diagonal s), Matrix.diagonal_mul_diagonal]
  simp only [pow_two]

/-- The original regularity premise is proved from the actual Gram characteristic roots. -/
lemma admissible_svd_regular (U : Mat 3) (s : Fin 3 → ℝ)
    (hs : Admissible s) (hsvd : HasSVD U s) : RegularData U := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hsvd
  constructor
  · have hp : P.det ≠ 0 := by
      intro hz
      have hh := orthogonal_abs_det hP
      simp [hz] at hh
    have hq : Q.det ≠ 0 := by
      intro hz
      have hh := orthogonal_abs_det hQ
      simp [hz] at hh
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero (mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr
      (fun i _ => ne_of_gt (admissible_pos hs i)))) hq
  · rw [svd_gram P Q s hP, Matrix.charpoly_mul_comm, orthogonal_cancel_left hQ,
      Matrix.charpoly_diagonal]
    rw [Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C]
      simpa using Multiset.Nodup.map (admissible_sq_injective hs) Finset.univ.nodup
    · exact Finset.prod_ne_zero_iff.mpr fun _ _ => Polynomial.X_sub_C_ne_zero _

end NLA.SP04

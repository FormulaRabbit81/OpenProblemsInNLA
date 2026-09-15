/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Definitions
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

lemma orthogonal_transpose {n : ℕ} {Q : Mat n} (hQ : Orthogonal Q) : Orthogonal Qᵀ := by
  simpa [Orthogonal] using And.intro hQ.2 hQ.1

lemma orthogonal_abs_det {n : ℕ} {Q : Mat n} (hQ : Orthogonal Q) : |Q.det| = 1 := by
  have hd := congrArg Matrix.det hQ.1
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  have ha : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, hd, abs_one]
  nlinarith [abs_nonneg Q.det]

lemma orthogonal_inverse_transport {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (X : Mat n) :
    Pᵀ * (P * X * Qᵀ) * Q = X := by
  calc
    Pᵀ * (P * X * Qᵀ) * Q = (Pᵀ * P) * X * (Qᵀ * Q) := by simp [Matrix.mul_assoc]
    _ = X := by rw [hP.1, hQ.1]; simp

lemma orthogonal_cancel_left {n : ℕ} {P : Mat n} (hP : Orthogonal P) (A : Mat n) :
    Pᵀ * (P * A) = A := by
  rw [← Matrix.mul_assoc, hP.1, Matrix.one_mul]

lemma feasible_orthogonal_iff {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (X : Mat n) :
    Feasible (P * X * Qᵀ) ↔ Feasible X := by
  simp [Feasible, Matrix.det_mul, abs_mul, orthogonal_abs_det hP, orthogonal_abs_det hQ]

/-- The literal entry sum is the trace of the Gram matrix; no norm instance is used. -/
lemma frobeniusSq_eq_trace {n : ℕ} (A : Mat n) :
    frobeniusSq A = Matrix.trace (Aᵀ * A) := by
  simp only [frobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

lemma frobeniusSq_orthogonal {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (A : Mat n) :
    frobeniusSq (P * A * Qᵀ) = frobeniusSq A := by
  rw [frobeniusSq_eq_trace, frobeniusSq_eq_trace]
  have hg : (P * A * Qᵀ)ᵀ * (P * A * Qᵀ) = Q * (Aᵀ * A) * Qᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc, orthogonal_cancel_left hP]
  rw [hg, Matrix.trace_mul_cycle]
  simp [hQ.1]

lemma frobeniusNorm_orthogonal {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (A : Mat n) :
    frobeniusNorm (P * A * Qᵀ) = frobeniusNorm A := by
  simp only [frobeniusNorm, frobeniusSq_orthogonal hP hQ]

lemma orthogonal_stationary_expression {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (U X : Mat n) :
    (P * X * Qᵀ)ᵀ * (P * U * Qᵀ - P * X * Qᵀ) =
      Q * (Xᵀ * (U - X)) * Qᵀ := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  simp [Matrix.transpose_mul, Matrix.mul_assoc, orthogonal_cancel_left hP]

lemma stationary_orthogonal_forward {n : ℕ} {P Q U X : Mat n} {c : ℝ}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (h : Stationary U X c) :
    Stationary (P * U * Qᵀ) (P * X * Qᵀ) c := by
  refine ⟨(feasible_orthogonal_iff hP hQ X).mpr h.1, ?_⟩
  rw [orthogonal_stationary_expression hP, h.2]
  simp [hQ.2]

lemma stationary_orthogonal_iff {n : ℕ} {P Q : Mat n}
    (hP : Orthogonal P) (hQ : Orthogonal Q) (U X : Mat n) (c : ℝ) :
    Stationary (P * U * Qᵀ) (P * X * Qᵀ) c ↔ Stationary U X c := by
  constructor
  · intro h
    have hh := stationary_orthogonal_forward (orthogonal_transpose hP) (orthogonal_transpose hQ) h
    simpa only [Matrix.transpose_transpose, orthogonal_inverse_transport hP hQ] using hh
  · exact stationary_orthogonal_forward hP hQ

lemma full_orthogonal_transport {n : ℕ} (P Q U X : Mat n) (c : ℝ)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    (Feasible (P * X * Qᵀ) ↔ Feasible X) ∧
    frobeniusNorm (P * (U - X) * Qᵀ) = frobeniusNorm (U - X) ∧
    (Stationary (P * U * Qᵀ) (P * X * Qᵀ) c ↔ Stationary U X c) :=
  ⟨feasible_orthogonal_iff hP hQ X, frobeniusNorm_orthogonal hP hQ (U-X),
    stationary_orthogonal_iff hP hQ U X c⟩

end NLA.SP04

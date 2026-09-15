/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Definitions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

lemma feasible_det_ne_zero {n : ℕ} {X : Mat n} (h : Feasible X) : X.det ≠ 0 := by
  intro hz
  simp [Feasible, hz] at h

lemma stationary_cross {n : ℕ} {U X : Mat n} {c : ℝ} (h : Stationary U X c) :
    Xᵀ * U = Xᵀ * X + c • (1 : Mat n) ∧
    Uᵀ * X = Xᵀ * X + c • (1 : Mat n) := by
  have h1 : Xᵀ * U = Xᵀ * X + c • (1 : Mat n) := by
    have hh := h.2
    rw [Matrix.mul_sub] at hh
    exact sub_eq_iff_eq_add'.mp hh
  refine ⟨h1, ?_⟩
  have hh := congrArg Matrix.transpose h1
  simpa using hh

lemma stationary_other_cross {n : ℕ} {U X : Mat n} {c : ℝ}
    (h : Stationary U X c) :
    U * Xᵀ = X * Xᵀ + c • (1 : Mat n) ∧
    X * Uᵀ = X * Xᵀ + c • (1 : Mat n) := by
  have hd : IsUnit X.det := isUnit_iff_ne_zero.mpr (feasible_det_ne_zero h.1)
  have hs := (stationary_cross h).2
  have hh := congrArg (fun A : Mat n => X * A * X⁻¹) hs
  have h2 : X * Uᵀ = X * Xᵀ + c • (1 : Mat n) := by
    simpa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv X hd] using hh
  refine ⟨?_, h2⟩
  have hh := congrArg Matrix.transpose h2
  simpa using hh

/-- The complete stationary equation forces Gram commutation, for every real multiplier. -/
lemma stationary_gram_commutes {n : ℕ} {U X : Mat n} {c : ℝ}
    (h : Stationary U X c) :
    (Xᵀ * X) * (Uᵀ * U) = (Uᵀ * U) * (Xᵀ * X) := by
  obtain ⟨h1, h2⟩ := stationary_cross h
  obtain ⟨h3, h4⟩ := stationary_other_cross h
  calc
    (Xᵀ * X) * (Uᵀ * U) = Xᵀ * (X * Uᵀ) * U := by simp [Matrix.mul_assoc]
    _ = Xᵀ * (X * Xᵀ + c • (1 : Mat n)) * U := by rw [h4]
    _ = (Xᵀ * X) * (Xᵀ * U) + c • (Xᵀ * U) := by
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = (Xᵀ * X) * (Xᵀ * X + c • (1 : Mat n)) + c • (Xᵀ * X + c • (1 : Mat n)) := by rw [h1]
    _ = (Xᵀ * X + c • (1 : Mat n)) * (Xᵀ * X) + c • (Xᵀ * X + c • (1 : Mat n)) := by
      simp [Matrix.mul_add, Matrix.add_mul]
    _ = (Uᵀ * X) * (Xᵀ * X) + c • (Uᵀ * X) := by rw [h2]
    _ = Uᵀ * (X * Xᵀ + c • (1 : Mat n)) * X := by
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = Uᵀ * (U * Xᵀ) * X := by rw [h3]
    _ = (Uᵀ * U) * (Xᵀ * X) := by simp [Matrix.mul_assoc]

lemma admissible_pos {s : Fin 3 → ℝ} (hs : Admissible s) : ∀ i, 0 < s i := by
  rcases hs with ⟨h0, h01, h12, h2⟩
  intro i
  fin_cases i <;> dsimp <;> linarith

lemma admissible_injective {s : Fin 3 → ℝ} (hs : Admissible s) : Function.Injective s := by
  rcases hs with ⟨h0, h01, h12, h2⟩
  intro i j heq
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; dsimp at heq; linarith)

lemma admissible_sq_injective {s : Fin 3 → ℝ} (hs : Admissible s) :
    Function.Injective (fun i => (s i) ^ 2) := by
  intro i j heq
  exact admissible_injective hs ((sq_eq_sq₀ (le_of_lt (admissible_pos hs i))
    (le_of_lt (admissible_pos hs j))).mp heq)

lemma stationary_diagonal_gram {s : Fin 3 → ℝ} (hs : Admissible s)
    {X : Mat 3} {c : ℝ} (h : Stationary (Matrix.diagonal s) X c) :
    ∀ i j, i ≠ j → (Xᵀ * X) i j = 0 := by
  have hc := stationary_gram_commutes h
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at hc
  intro i j hij
  have heq := congrArg (fun A : Mat 3 => A i j) hc
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at heq
  have hne : (s j) ^ 2 - (s i) ^ 2 ≠ 0 := by
    intro hz
    exact hij ((admissible_sq_injective hs (sub_eq_zero.mp hz)).symm)
  have hp : (Xᵀ * X) i j * ((s j) ^ 2 - (s i) ^ 2) = 0 := by nlinarith [heq]
  exact (mul_eq_zero.mp hp).resolve_right hne

/-- No off-diagonal stationary matrices are omitted, regardless of multiplier sign. -/
lemma stationary_diagonal_matrix {s : Fin 3 → ℝ} (hs : Admissible s)
    {X : Mat 3} {c : ℝ} (h : Stationary (Matrix.diagonal s) X c) :
    X = Matrix.diagonal (fun i => X i i) := by
  have hg := stationary_diagonal_gram hs h
  have hc := (stationary_cross h).1
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have heq := congrArg (fun A : Mat 3 => A j i) hc
    simp [Matrix.mul_diagonal, hg j i (Ne.symm hij), Matrix.one_apply_ne (Ne.symm hij)] at heq
    have hx : X i j = 0 := heq.resolve_right (ne_of_gt (admissible_pos hs i))
    simp [hij, hx]

/-- Exact full-matrix/scalar correspondence used by the independently reviewed target. -/
lemma all_diagonal_stationary_iff (s : Fin 3 → ℝ) (hs : Admissible s)
    (X : Mat 3) (c : ℝ) :
    Stationary (Matrix.diagonal s) X c ↔
      ∃ x : Fin 3 → ℝ, X = Matrix.diagonal x ∧
        (∀ i, (x i) ^ 2 - s i * x i + c = 0) ∧ |∏ i, x i| = 1 := by
  constructor
  · intro h
    have hX := stationary_diagonal_matrix hs h
    refine ⟨fun i => X i i, hX, ?_, ?_⟩
    · intro i
      have heq := h.2
      rw [hX] at heq
      have hi := congrArg (fun A : Mat 3 => A i i) heq
      simp at hi
      nlinarith [hi]
    · have hd := h.1
      rw [hX] at hd
      simpa [Feasible, Matrix.det_diagonal] using hd
  · rintro ⟨x, rfl, hquad, hprod⟩
    refine ⟨?_, ?_⟩
    · simpa [Feasible, Matrix.det_diagonal] using hprod
    · ext i j
      by_cases hij : i = j
      · subst j
        simp
        nlinarith [hquad i]
      · simp [hij]

end NLA.SP04

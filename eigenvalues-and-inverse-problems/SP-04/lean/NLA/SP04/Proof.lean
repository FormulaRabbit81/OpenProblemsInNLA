/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
Complete proof implementation of the independently reviewed eleven declarations.
-/
import NLA.SP04.Witness
import NLA.SP04.Spectrum
import NLA.SP04.Generic

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

/-- Exact constants used to exclude every nonnegative multiplier of competing size. -/
theorem numerical_bounds :
    (99 / 100 : ℝ) ^ 2 < 49 / 16 - 52 / 25 ∧
    (275 / 198 : ℝ) < 2 ∧
    (13 / 25 : ℝ) * (44 / 25) * (51 / 50) < 1 ∧
    (201 / 400 : ℝ) < 13 / 25 := by
  exact scalar_numerical_bounds

/-- Reduction of every real stationary matrix, not just an explicit diagonal candidate. -/
theorem diagonal_stationary_iff (s : Fin 3 → ℝ) (hs : Admissible s)
    (X : Mat 3) (c : ℝ) :
    Stationary (Matrix.diagonal s) X c ↔
      ∃ x : Fin 3 → ℝ, X = Matrix.diagonal x ∧
        (∀ i, (x i) ^ 2 - s i * x i + c = 0) ∧ |∏ i, x i| = 1 := by
  exact all_diagonal_stationary_iff s hs X c

/-- Unique least-absolute selection and a strictly better feasible matrix throughout the source box. -/
theorem diagonal_counterexample (s : Fin 3 → ℝ) (hs : Admissible s) :
    ∃ t : ℝ, 0 < t ∧ t < 13 / 25 ∧
      UniqueLeastStationary (Matrix.diagonal s) (selectedMatrix s t) (-t) ∧
      Feasible (improvedMatrix s t) ∧
      frobeniusNorm (Matrix.diagonal s - improvedMatrix s t) <
        frobeniusNorm (Matrix.diagonal s - selectedMatrix s t) := by
  exact diagonal_counterexample_full s hs

/-- Finiteness of the entire stationary set, including all multipliers and both determinant signs. -/
theorem diagonal_finite (s : Fin 3 → ℝ) (hs : Admissible s) :
    (stationaryPairs (Matrix.diagonal s)).Finite := by
  exact diagonal_stationary_finite s hs

/-- Literal two-sided orthogonal transport of the full constraint, norm and stationary equation. -/
theorem orthogonal_transport {n : ℕ} (P Q U X : Mat n) (c : ℝ)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    (Feasible (P * X * Qᵀ) ↔ Feasible X) ∧
    frobeniusNorm (P * (U - X) * Qᵀ) = frobeniusNorm (U - X) ∧
    (Stationary (P * U * Qᵀ) (P * X * Qᵀ) c ↔ Stationary U X c) := by
  exact full_orthogonal_transport P Q U X c hP hQ

/-- Six polynomial signs yield a nonempty open set and a true SVD in the original singular-value box. -/
theorem spectral_family :
    IsOpen counterexampleFamily ∧ sampleMatrix ∈ counterexampleFamily ∧
      ∀ U ∈ counterexampleFamily, ∃ s : Fin 3 → ℝ, Admissible s ∧ HasSVD U s := by
  exact ⟨family_isOpen, sample_in_family, family_has_admissible_svd⟩

/-- These data are invertible and have genuinely distinct squared singular values. -/
theorem regular_svd (U : Mat 3) (s : Fin 3 → ℝ)
    (hs : Admissible s) (hsvd : HasSVD U s) : RegularData U := by
  exact admissible_svd_regular U s hs hsvd

/-- Every matrix in the open family has a finite full stationary set and a unique failing selection. -/
theorem open_family_counterexamples : ∀ U ∈ counterexampleFamily, SelectionFails U := by
  intro U hU
  obtain ⟨s, hs, hsvd⟩ := family_has_admissible_svd U hU
  exact selectionFails_of_admissible_svd U s hs hsvd (admissible_svd_regular U s hs hsvd)

/-- A proper polynomial zero-set cannot contain a nonempty open set of real matrices. -/
theorem algebraic_avoidance (S : Set (Mat 3)) (hS : IsOpen S) (hne : S.Nonempty)
    (p : MvPolynomial (Fin 3 × Fin 3) ℝ) (hp : p ≠ 0) :
    ∃ U ∈ S, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 := by
  exact polynomial_avoids_open S hS hne p hp

/-- Every possible proper real algebraic exception leaves a complete regular counterexample. -/
theorem generic_counterexamples (p : MvPolynomial (Fin 3 × Fin 3) ℝ) (hp : p ≠ 0) :
    ∃ U : Mat 3, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 ∧ SelectionFails U := by
  obtain ⟨U, hU, hpU⟩ := algebraic_avoidance counterexampleFamily family_isOpen
    ⟨sampleMatrix, sample_in_family⟩ p hp
  exact ⟨U, hpU, open_family_counterexamples U hU⟩

/-- The full original rule, across all dimensions and algebraically generic data, is false. -/
theorem canonical_counterexample : ¬ AllGenericSelectionRules := by
  intro hall
  obtain ⟨p, hp, hrule⟩ := hall 3 (by norm_num)
  obtain ⟨U, hpU, hreg, hfin, X, c, hleast, Y, hY, hbetter⟩ := generic_counterexamples p hp
  exact (not_lt_of_ge ((hrule U hpU hreg hfin X c hleast).2 Y hY)) hbetter

#assert_trust kernel numerical_bounds
#print axioms numerical_bounds
#assert_trust kernel diagonal_stationary_iff
#print axioms diagonal_stationary_iff
#assert_trust kernel diagonal_counterexample
#print axioms diagonal_counterexample
#assert_trust kernel diagonal_finite
#print axioms diagonal_finite
#assert_trust kernel orthogonal_transport
#print axioms orthogonal_transport
#assert_trust kernel spectral_family
#print axioms spectral_family
#assert_trust kernel regular_svd
#print axioms regular_svd
#assert_trust kernel open_family_counterexamples
#print axioms open_family_counterexamples
#assert_trust kernel algebraic_avoidance
#print axioms algebraic_avoidance
#assert_trust kernel generic_counterexamples
#print axioms generic_counterexamples
#assert_trust kernel canonical_counterexample
#print axioms canonical_counterexample

end NLA.SP04

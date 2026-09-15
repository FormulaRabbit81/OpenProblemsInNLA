/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
This file defines the literal target; it contains no proof implementation.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Both determinant signs, exactly as in the canonical problem. -/
def Feasible {n : ℕ} (X : Mat n) : Prop := |X.det| = 1

/-- The actual sum-of-squares Frobenius norm, with its nonnegative square root. -/
def frobeniusSq {n : ℕ} (X : Mat n) : ℝ := ∑ i, ∑ j, (X i j) ^ 2

def frobeniusNorm {n : ℕ} (X : Mat n) : ℝ := Real.sqrt (frobeniusSq X)

/-- Every real stationary matrix and its real multiplier, without diagonal restrictions. -/
def Stationary {n : ℕ} (U X : Mat n) (c : ℝ) : Prop :=
  Feasible X ∧ Xᵀ * (U - X) = c • (1 : Mat n)

def stationaryPairs {n : ℕ} (U : Mat n) : Set (Mat n × ℝ) :=
  {p | Stationary U p.1 p.2}

/-- Unique minimizing pair, compared with the entire real stationary set. -/
def UniqueLeastStationary {n : ℕ} (U X : Mat n) (c : ℝ) : Prop :=
  Stationary U X c ∧ ∀ Y d, Stationary U Y d →
    |c| ≤ |d| ∧ (|c| = |d| → Y = X ∧ d = c)

/-- Actual global nearestness, including attainment at the displayed feasible matrix. -/
def IsNearest {n : ℕ} (U X : Mat n) : Prop :=
  Feasible X ∧ ∀ Y, Feasible Y → frobeniusNorm (U - X) ≤ frobeniusNorm (U - Y)

/-- Invertibility and distinct squared singular values: the real Gram polynomial has no repeated roots. -/
def RegularData {n : ℕ} (U : Mat n) : Prop :=
  U.det ≠ 0 ∧ (Uᵀ * U).charpoly.roots.Nodup

/-- The complete selection claim outside one arbitrary proper real algebraic exception.
The finite and regular premises retain the stated generic domain. -/
def GenericSelectionRule (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n × Fin n) ℝ, p ≠ 0 ∧
    ∀ U : Mat n, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 →
      RegularData U → (stationaryPairs U).Finite →
      ∀ X c, UniqueLeastStationary U X c → IsNearest U X

def AllGenericSelectionRules : Prop := ∀ n : ℕ, 2 ≤ n → GenericSelectionRule n

/-- Both orthogonality equations, over all real matrices and either orientation. -/
def Orthogonal {n : ℕ} (Q : Mat n) : Prop := Qᵀ * Q = 1 ∧ Q * Qᵀ = 1

/-- A genuine two-sided orthogonal singular-value decomposition. -/
def HasSVD (U : Mat 3) (s : Fin 3 → ℝ) : Prop :=
  ∃ P Q : Mat 3, Orthogonal P ∧ Orthogonal Q ∧ U = P * Matrix.diagonal s * Qᵀ

def Admissible (s : Fin 3 → ℝ) : Prop :=
  (7 : ℝ) / 4 < s 0 ∧ s 0 < s 1 ∧ s 1 < s 2 ∧ s 2 < (44 : ℝ) / 25

def largeRoot (s c : ℝ) : ℝ := (s + Real.sqrt (s ^ 2 - 4 * c)) / 2

def positiveRoot (s t : ℝ) : ℝ := (s + Real.sqrt (s ^ 2 + 4 * t)) / 2

def negativeMagnitude (s t : ℝ) : ℝ := (Real.sqrt (s ^ 2 + 4 * t) - s) / 2

def selectedEntries (s : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![-negativeMagnitude (s 0) t, positiveRoot (s 1) t, positiveRoot (s 2) t]

def improvedEntries (s : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![negativeMagnitude (s 0) t, positiveRoot (s 1) t, positiveRoot (s 2) t]

def selectedMatrix (s : Fin 3 → ℝ) (t : ℝ) : Mat 3 := Matrix.diagonal (selectedEntries s t)

def improvedMatrix (s : Fin 3 → ℝ) (t : ℝ) : Mat 3 := Matrix.diagonal (improvedEntries s t)

def sampleSingularValues : Fin 3 → ℝ := ![1751/1000, 1755/1000, 1759/1000]

def sampleMatrix : Mat 3 := Matrix.diagonal sampleSingularValues

/-- Three disjoint intervals for the singular values, strictly ordered within the source box. -/
def lowerEndpoint : Fin 3 → ℝ := ![1750/1000, 1754/1000, 1758/1000]

def upperEndpoint : Fin 3 → ℝ := ![1752/1000, 1756/1000, 1760/1000]

def gramPolynomialValue (U : Mat 3) (z : ℝ) : ℝ :=
  (z • (1 : Mat 3) - Uᵀ * U).det

/-- A full nine-dimensional open family described only by six strict polynomial signs. -/
def counterexampleFamily : Set (Mat 3) :=
  {U | ∀ i : Fin 3,
    gramPolynomialValue U ((lowerEndpoint i) ^ 2) *
      gramPolynomialValue U ((upperEndpoint i) ^ 2) < 0}

/-- A complete failure witness; finiteness, generic regularity and unique selection are proved. -/
def SelectionFails (U : Mat 3) : Prop :=
  RegularData U ∧ (stationaryPairs U).Finite ∧
    ∃ X : Mat 3, ∃ c : ℝ, UniqueLeastStationary U X c ∧
      ∃ Y : Mat 3, Feasible Y ∧ frobeniusNorm (U - Y) < frobeniusNorm (U - X)

end NLA.SP04

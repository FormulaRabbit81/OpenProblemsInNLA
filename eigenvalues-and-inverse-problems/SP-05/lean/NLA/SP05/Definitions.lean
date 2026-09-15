/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
Statement preparation only; no proof implementation.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Vec

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP05

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := (Fin n × Fin n) → ℝ
abbrev Operator (n : ℕ) := Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ

/-- Column vectorization uses the actual Mathlib convention: (column,row). -/
abbrev columnVec {n : ℕ} (X : Mat n) : Vec n := Matrix.vec X

/-- The actual commutation permutation matrix, swapping row and column indices. -/
def commutationMatrix (n : ℕ) : Operator n :=
  fun i j => if i = j.swap then 1 else 0

def frobeniusSq {n : ℕ} (X : Mat n) : ℝ := ∑ i, ∑ j, (X i j)^2

/-- Literal real Rayleigh quotient; target vectors are always nonzero. -/
def rayleigh {n : ℕ} (K : Operator n) (v : Vec n) : ℝ :=
  dotProduct v (K *ᵥ v) / dotProduct v v

def jordanMatrix {n : ℕ} (A B : Mat n) : Operator n :=
  Matrix.kronecker A B + Matrix.kronecker B A

/-- All quotient values in the specified eigenspace of the actual commutation matrix. -/
def sectorValues {n : ℕ} (A B : Mat n) (ε : ℝ) : Set ℝ :=
  {r | ∃ v : Vec n, v ≠ 0 ∧ commutationMatrix n *ᵥ v = ε • v ∧
    r = rayleigh (Matrix.kronecker A B) v}

/-- A fixed skew-symmetric witness; its first two coordinates exist when n≥2. -/
def skewExample (n : ℕ) : Mat n := fun i j =>
  if i.val = 0 ∧ j.val = 1 then 1 else if i.val = 1 ∧ j.val = 0 then -1 else 0

end NLA.SP05

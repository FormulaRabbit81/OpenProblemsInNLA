/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences,
California Institute of Technology.

The original mathematical resolution is George Stepaniants's 11 September
2026 proof. This formalization uses substantial OpenAI Codex assistance.
The padded Schur-trajectory and finite-maximum design is adapted from the
same author's retained IE-05 Definitions.lean at upstream c7f399b1694e0a68756e8d060e2a71775c044301.
This independent statement boundary imports no solution or numerical tactic.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option autoImplicit false
noncomputable section
open scoped NNReal

namespace NLA.IE15

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The selected active row and column at each stage. No tie rule is imposed. -/
abbrev PivotPath (n : ℕ) := Fin n → Fin n × Fin n

/-- The two literal interchanges specified by Gaussian elimination. -/
def pivotSwap {n : ℕ} (S : Mat n) (k r c : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k r i) (Equiv.swap k c j)

/-- The actual trailing Schur complement, padded with zeros outside its active block.
`AdmissiblePivot` excludes zero divisors; Lean's total division adds no valid paths. -/
def schurStep {n : ℕ} (S : Mat n) (k r c : Fin n) : Mat n :=
  let B := pivotSwap S k r c
  fun i j => if k < i ∧ k < j then
    B i j - (B i k / B k k) * B k j else 0

/-- Stage zero is the input; stages `0,...,n-1` are precisely the active matrices. -/
def trajectory {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (trajectory A path k) ⟨k, h⟩ (path ⟨k, h⟩).1 (path ⟨k, h⟩).2
    else 0

/-- A nonzero active entry maximal in its own active row and column, including ties. -/
def AdmissiblePivot {n : ℕ} (S : Mat n) (k r c : Fin n) : Prop :=
  k ≤ r ∧ k ≤ c ∧ S r c ≠ 0 ∧
    (∀ j, k ≤ j → |S r j| ≤ |S r c|) ∧
    (∀ i, k ≤ i → |S i c| ≤ |S r c|)

def AdmissiblePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, AdmissiblePivot (trajectory A path k.val) k (path k).1 (path k).2

def noSwapPath (n : ℕ) : PivotPath n := fun k => (k, k)

/-- Finite maximum of absolute real entries, via the supremum in nonnegative reals. -/
def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

def activeMax {n : ℕ} (S : Mat n) (k : ℕ) : ℝ := activeMaxNN S k

/-- All active entries at all `n` stages contribute, including the unmodified input. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n =>
    activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) / entryMax A

/-- The exact canonical supremum domain: real nonsingular inputs and every rook path. -/
def growthSet (n : ℕ) : Set ℝ :=
  {r | ∃ A : Mat n, A.det ≠ 0 ∧
    ∃ path : PivotPath n, AdmissiblePath A path ∧ r = growth A path}

/-- This real supremum will be accompanied by explicit greatest-element theorems. -/
def rookGrowthSup (n : ℕ) : ℝ := sSup (growthSet n)

def witness3 : Mat 3 :=
  !![1, 0, -1; 0, 1, -1; 1, 1, 1]

def witness4 : Mat 4 :=
  !![1, 0, 1, 1; 0, 1, 1/3, -1; -1/3, -1, 1, -1; -1, 1, 1, 1]

end NLA.IE15

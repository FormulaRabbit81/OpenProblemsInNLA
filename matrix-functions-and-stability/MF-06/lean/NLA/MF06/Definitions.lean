/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Statement draft; no MF-06 proof is claimed.

Original MF-06 solution: George Stepaniants, solution.md at the canonical
matrix-functions-and-stability/MF-06 page. The original question is attributed
to Epperlein and Wirth; its cited extremal-norm and nonresonance background
retains the attribution to Barabanov/Wirth, Chitour--Mason--Sigalotti and Morris.
The unchanged MF05/MF07 definitions and existing proofs retain Matthew J.
Colbrook's mathematical attribution and their own source authorship.

Every definition below is an actual matrix, set, norm expression, finite
coordinate map or elementary predicate. No flag, extremal norm, stability
theorem, exterior estimate or perturbation theorem is supplied as an oracle.
-/
import NLA.MF05.Definitions
import Mathlib.Analysis.Seminorm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.UniformSpace.Dini

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

/-- Uniform boundedness of all actual words, including the empty word. -/
def IsProductBounded {d : ℕ} (M : Set (Square d)) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, familyGrowth M n ≤ K

/-- Invariance under every original generator, on the actual complex space. -/
def FamilyInvariant {d : ℕ} (M : Set (Square d))
    (S : Submodule ℂ (EuclideanVector d)) : Prop :=
  ∀ A ∈ M, ∀ x : EuclideanVector d, x ∈ S → applyMatrix A x ∈ S

def FamilyIrreducible {d : ℕ} (M : Set (Square d)) : Prop :=
  ∀ S : Submodule ℂ (EuclideanVector d), FamilyInvariant M S → S = ⊥ ∨ S = ⊤

/-- The actual, undiscounted all-word envelope. Its norm laws are conclusions. -/
def boundedEnvelope {d : ℕ} (M : Set (Square d)) (x : EuclideanVector d) : ℝ :=
  productEnvelope M (fun A => A) 1 x

def tailValues {d : ℕ} (M : Set (Square d)) (n : ℕ)
    (x : EuclideanVector d) : Set ℝ :=
  {r | ∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
    r = boundedEnvelope M (applyMatrix (matrixProduct w) x)}

def tailEnvelope {d : ℕ} (M : Set (Square d)) (n : ℕ)
    (x : EuclideanVector d) : ℝ :=
  sSup (tailValues M n x)

/-- The decreasing-tail infimum; no continuity or nontriviality is built in. -/
def stableGauge {d : ℕ} (M : Set (Square d)) (x : EuclideanVector d) : ℝ :=
  sInf (Set.range (fun n : ℕ => tailEnvelope M n x))

/-- Norms of actual restricted word actions. Inserting zero makes the zero
subspace case explicit; it does not assert an invariant-subspace property. -/
def restrictedGrowth {d : ℕ} (M : Set (Square d))
    (S : Submodule ℂ (EuclideanVector d)) (n : ℕ) : ℝ :=
  sSup (insert 0 {r | ∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
    ∃ x : EuclideanVector d, x ∈ S ∧ ‖x‖ = 1 ∧
      r = ‖applyMatrix (matrixProduct w) x‖})

def coneHeight (q K : ℝ) : ℝ := (K + 1) / (1 - q)

def coneLoss (q K : ℝ) : ℝ := coneHeight q K + 1

/-- R is required to be an actual two-sided inverse of Q by every contract
that uses this image as a change of basis. -/
def conjugateFamily {d : ℕ} (Q R : Square d) (M : Set (Square d)) : Set (Square d) :=
  (fun A : Square d => R * A * Q) '' M

/-- A block labeling partitions coordinates into its literal fibers. -/
abbrev BlockIndex {d r : ℕ} (b : Fin d → Fin r) (i : Fin r) :=
  {j : Fin d // b j = i}

def blockDim {d r : ℕ} (b : Fin d → Fin r) (i : Fin r) : ℕ :=
  Fintype.card (BlockIndex b i)

def blockCoordinate {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (j : Fin (blockDim b i)) : Fin d :=
  ((Fintype.equivFin (BlockIndex b i)).symm j).val

def blockMatrix {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (A : Square d) : Square (blockDim b i) :=
  fun u v => A (blockCoordinate b i u) (blockCoordinate b i v)

def diagonalFamily {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (M : Set (Square d)) : Set (Square (blockDim b i)) :=
  (blockMatrix b i) '' M

def IsUpperBlockTriangular {d r : ℕ} (b : Fin d → Fin r) (A : Square d) : Prop :=
  ∀ i j : Fin d, b j < b i → A i j = 0

/-- The genuine basis index of an exterior power, including degrees zero
and greater than the dimension. No exterior matrix is assumed in a field. -/
abbrev ExteriorIndex (d k : ℕ) := Set.powersetCard (Fin d) k

def compoundDim (d k : ℕ) : ℕ := Fintype.card (ExteriorIndex d k)

def compoundIndex (d k : ℕ) (i : Fin (compoundDim d k)) : ExteriorIndex d k :=
  (Fintype.equivFin (ExteriorIndex d k)).symm i

def minorCoordinate (d k : ℕ) (i : Fin (compoundDim d k)) : Fin k ↪o Fin d :=
  Set.powersetCard.ofFinEmbEquiv.symm (compoundIndex d k i)

/-- All sorted k-by-k minors. The independent coordinate contract identifies
this literal matrix with `exteriorPower.map` in the standard exterior basis. -/
def compoundMatrix {d : ℕ} (k : ℕ) (A : Square d) : Square (compoundDim d k) :=
  fun i j => Matrix.det (A.submatrix (minorCoordinate d k i) (minorCoordinate d k j))

def compoundFamily {d : ℕ} (k : ℕ) (M : Set (Square d)) :
    Set (Square (compoundDim d k)) :=
  (compoundMatrix k) '' M

/-- Finite dimensional constants stay symbolic; no permutation enumeration
or interval computation is part of their definition or intended proof. -/
def compoundNormConstant (d k : ℕ) : ℝ :=
  (compoundDim d k : ℝ) * (Nat.factorial k : ℝ)

def compoundLipschitzConstant (d k : ℕ) (L : ℝ) : ℝ :=
  (compoundDim d k : ℝ) * (k : ℝ) * (Nat.factorial k : ℝ) * L ^ (k - 1)

/-- Literal Kronecker entries, reindexed by the standard product equivalence. -/
def tensorMatrix {m n : ℕ} (A : Square m) (B : Square n) : Square (m * n) :=
  (Matrix.kronecker A B).submatrix
    (finProdFinEquiv (m := m) (n := n)).symm
    (finProdFinEquiv (m := m) (n := n)).symm

/-- Both tensor factors come from the SAME original generator. -/
def pairedFamily {d m n : ℕ} (M : Set (Square d))
    (f : Square d → Square m) (g : Square d → Square n) : Set (Square (m * n)) :=
  (fun A : Square d => tensorMatrix (f A) (g A)) '' M

abbrev Allocation {d r : ℕ} (b : Fin d → Fin r) :=
  ∀ i : Fin r, Fin (blockDim b i + 1)

def allocationDegree {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) : ℕ :=
  ∑ i : Fin r, (a i).val

abbrev DegreeAllocation {d r : ℕ} (b : Fin d → Fin r) (k : ℕ) :=
  {a : Allocation b // allocationDegree b a = k}

def allocationMax {d r : ℕ} {b : Fin d → Fin r} (a c : Allocation b) : Allocation b :=
  fun i => max (a i) (c i)

def allocationMin {d r : ℕ} {b : Fin d → Fin r} (a c : Allocation b) : Allocation b :=
  fun i => min (a i) (c i)

/-- A genuine finite tensor-product coordinate index, with degree-zero
factors retained as one-dimensional spaces. -/
abbrev AllocationIndex {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) :=
  ∀ i : Fin r, Fin (compoundDim (blockDim b i) (a i).val)

def allocationDim {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b) : ℕ :=
  Fintype.card (AllocationIndex b a)

def allocationCoordinate {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (j : Fin (allocationDim b a)) : AllocationIndex b a :=
  (Fintype.equivFin (AllocationIndex b a)).symm j

/-- Every factor is an actual compound of one original A's diagonal blocks.
There is no independent choice of a generator in different tensor factors. -/
def allocationMatrix {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (A : Square d) : Square (allocationDim b a) :=
  fun u v => ∏ i : Fin r,
    compoundMatrix (a i).val (blockMatrix b i A)
      (allocationCoordinate b a u i) (allocationCoordinate b a v i)

def allocationFamily {d r : ℕ} (b : Fin d → Fin r) (a : Allocation b)
    (M : Set (Square d)) : Set (Square (allocationDim b a)) :=
  (allocationMatrix b a) '' M

end NLA.MF06

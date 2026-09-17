/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Nobori's original question, Audenaert's
refined commutator theorem, and the repository reduction retain their attribution.

Definitions only. Norms and singular values are the genuine Euclidean objects.
No SVD, spectral maximum, inequality or padding theorem is assumed here.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace NLA.MI13
noncomputable section
open scoped BigOperators Matrix

abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ
abbrev Square (r : ℕ) := Rect r r
abbrev EuclideanVector (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev EntrySpace (m n : ℕ) := EuclideanSpace ℂ (Fin m × Fin n)

def euclideanLin {m n : ℕ} (A : Rect m n) :
    EuclideanVector n →ₗ[ℂ] EuclideanVector m := Matrix.toEuclideanLin A

def euclideanCLM {m n : ℕ} (A : Rect m n) :
    EuclideanVector n →L[ℂ] EuclideanVector m :=
  (euclideanLin A).toContinuousLinearMap

def spectralNorm {m n : ℕ} (A : Rect m n) : ℝ := ‖euclideanCLM A‖

def flatten {m n : ℕ} (A : Rect m n) : EntrySpace m n :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

def frobeniusNorm {m n : ℕ} (A : Rect m n) : ℝ := ‖flatten A‖

def hsInner {r : ℕ} (Y Z : Square r) : ℂ := inner ℂ (flatten Y) (flatten Z)

/-- Mathlib's actual decreasing, nonnegative, zero-extended singular values. -/
def singularValue {m n : ℕ} (A : Rect m n) (k : ℕ) : ℝ :=
  (euclideanLin A).singularValues k

def gramEigenvalue {m n : ℕ} (A : Rect m n) (i : Fin n) : ℝ :=
  (euclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues
    (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)) i

def IsUnitary {r : ℕ} (U : Square r) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

def singularDiagonal {r : ℕ} (A : Square r) : Square r :=
  Matrix.diagonal (fun i => (singularValue A i.val : ℂ))

/-- A property of a supplied basis; its existence is an explicit contract. -/
def GramBasis {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℂ (EuclideanVector r)) : Prop :=
  ∀ i, (euclideanLin A).adjoint (euclideanLin A (v i)) =
    ((singularValue A i.val : ℂ) ^ 2) • v i

def positiveSingularIndices {r : ℕ} (A : Square r) : Set (Fin r) :=
  {i | 0 < singularValue A i.val}

def normalizedImages {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℂ (EuclideanVector r)) (i : Fin r) :
    EuclideanVector r := (singularValue A i.val : ℂ)⁻¹ • euclideanLin A (v i)

def commutator {r : ℕ} (X Y : Square r) : Square r := X * Y - Y * X
def commutatorT {r : ℕ} (X Y : Square r) : Square r :=
  commutator X.conjTranspose (commutator X Y)
def commutatorJ {r : ℕ} (X Y : Square r) : Square r :=
  commutator X.conjTranspose Y.conjTranspose

/-- Coefficients on the actual Hilbert space of matrix entries. -/
def commutatorCoefficients {r : ℕ} (X : Square r) :
    Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ := fun ij kl =>
  (if kl.2 = ij.2 then X ij.1 kl.1 else 0) -
    (if ij.1 = kl.1 then X kl.2 ij.2 else 0)

def commutatorOperator {r : ℕ} (X : Square r) :
    EntrySpace r r →L[ℂ] EntrySpace r r :=
  (Matrix.toEuclideanLin (commutatorCoefficients X)).toContinuousLinearMap

/-- Total at r=0; the commutator target itself has r at least two. -/
def firstEntry {r : ℕ} (A : Square r) : ℂ :=
  if h : 0 < r then A ⟨0, h⟩ ⟨0, h⟩ else 0

def circlePlus (d : ℝ) : ℂ :=
  (d : ℂ) + Complex.I * (Real.sqrt (1 - d ^ 2) : ℂ)
def circleMinus (d : ℝ) : ℂ :=
  (d : ℂ) - Complex.I * (Real.sqrt (1 - d ^ 2) : ℂ)

/-- Sum-index zero padding, reindexed to an ordinary square Fin matrix. -/
def padUpper {m n : ℕ} (A : Rect m n) : Square (m + n) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (0 : Square m) A (0 : Rect n m) (0 : Square n))

def padLower {m n : ℕ} (B : Rect n m) : Square (m + n) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (0 : Square m) (0 : Rect m n) B (0 : Square n))

def sharpA : Square 2 := Matrix.diagonal (fun i => if i = 0 then 1 else -1)
def sharpC : Square 2 := fun i j => if i = 0 ∧ j = 1 then 1 else 0

end
end NLA.MI13

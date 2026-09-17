/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original problem and special-case attribution
to Tichý, Liesen, and Faber, the Faber–Liesen–Tichý approximation background, and
the Courtney–Sarason interpolation background are retained.

Concrete definitions only. No interpolation, factorization, minimax, or
attainment theorem is assumed. The norms are actual Euclidean norms.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

namespace NLA.IE02
noncomputable section
open scoped BigOperators Matrix
open Polynomial

abbrev Poly := Polynomial ℂ
abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev H (n : ℕ) := EuclideanSpace ℂ (Fin n)

def DegreeLE (p : Poly) (m : ℕ) : Prop := p.degree ≤ (m : WithBot ℕ)
def DegreeLT (p : Poly) (n : ℕ) : Prop := p = 0 ∨ p.natDegree < n

def coeffVector (n : ℕ) (p : Poly) : H n :=
  WithLp.toLp 2 (fun i => p.coeff i.val)

def vectorPolynomial {n : ℕ} (v : H n) : Poly :=
  ∑ i : Fin n, C (v i) * X ^ i.val

def truncate (n : ℕ) (p : Poly) : Poly := vectorPolynomial (coeffVector n p)

def toeplitz (n : ℕ) (p : Poly) : Square n :=
  fun i j => if j.val ≤ i.val then p.coeff (i.val - j.val) else 0

def IsToeplitz {n : ℕ} (A : Square n) : Prop := ∃ p : Poly, A = toeplitz n p
def shift (n : ℕ) : Square n := toeplitz n X

def euclideanLin {n : ℕ} (A : Square n) : H n →ₗ[ℂ] H n := Matrix.toEuclideanLin A
def euclideanCLM {n : ℕ} (A : Square n) : H n →L[ℂ] H n :=
  (euclideanLin A).toContinuousLinearMap
def operatorNorm {n : ℕ} (A : Square n) : ℝ := ‖euclideanCLM A‖

def unitSphere (n : ℕ) : Set (H n) := {x | ‖x‖ = 1}

def maximalSpace {n : ℕ} (A : Square n) : Submodule ℂ (H n) :=
  LinearMap.ker ((euclideanLin A).adjoint ∘ₗ euclideanLin A -
    (((operatorNorm A ^ 2 : ℝ) : ℂ) • LinearMap.id))

def unitMaximal {n : ℕ} (A : Square n) : Set (H n) :=
  {x | x ∈ maximalSpace A ∧ x ∈ unitSphere n}

def finiteInverse {n : ℕ} (α : ℂ) (K : Square n) : Square n :=
  α⁻¹ • ∑ j : Fin n, (-α⁻¹ • K) ^ j.val

def schurM {n : ℕ} (U : Square n) (c : ℂ) : Square n := 1 - star c • U
def schurZ {n : ℕ} (U : Square n) (c : ℂ) (B : Square n) : Square n :=
  (U - c • 1) * B

def activeBlock {n : ℕ} (Z : Square (n + 1)) : Square n :=
  fun i j => Z i.succ j.castSucc

def appendVector {n : ℕ} (g : H n) (η : ℂ) : H (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => g i) η)

def prependZero {n : ℕ} (g : H n) : H (n + 1) :=
  WithLp.toLp 2 (Fin.cons 0 (fun i => g i))

def schurNumerator (c : ℂ) (a b : Poly) : Poly := C c * b + X * a
def schurDenominator (c : ℂ) (a b : Poly) : Poly := b + C (star c) * X * a

/-- Properties of supplied data; their existence is an independent contract. -/
def SchurPair (n : ℕ) (U : Square n) (d : ℕ) (a b : Poly) : Prop :=
  d < n ∧ a.degree = (d : WithBot ℕ) ∧ DegreeLE b d ∧ b.coeff 0 = 1 ∧
  IsCoprime a b ∧
  (∀ z : ℂ, ‖z‖ ≤ 1 → b.eval z ≠ 0 ∧ ‖a.eval z‖ ≤ ‖b.eval z‖) ∧
  (∀ z : ℂ, ‖z‖ = 1 → ‖a.eval z‖ = ‖b.eval z‖) ∧
  U * toeplitz n b = toeplitz n a ∧
  (∀ x : H n, x ∈ maximalSpace U ↔
    ∃ h : Poly, DegreeLE h (n - 1 - d) ∧ x = coeffVector n (b * h)) ∧
  (∀ h : Poly, DegreeLE h (n - 1 - d) →
    euclideanLin U (coeffVector n (b * h)) = coeffVector n (a * h)) ∧
  Module.finrank ℂ (maximalSpace U) = n - d

def conjReflect (m : ℕ) (p : Poly) : Poly :=
  Polynomial.reflect m (p.map (starRingEnd ℂ))

def weightedFold (w : ℝ) (p : Poly) : Poly := C (Real.sqrt w : ℂ) * p
def sumSquares {l : ℕ} (q : Fin l → Poly) (z : ℂ) : ℝ := ∑ j, ‖(q j).eval z‖ ^ 2

def fourierCoeff {l : ℕ} (m : ℕ) (q : Fin l → Poly) (r : ℤ) : ℂ :=
  ∑ j, ∑ u : Fin (m + 1), ∑ v : Fin (m + 1),
    if (u.val : ℤ) - (v.val : ℤ) = r then
      (q j).coeff u.val * star ((q j).coeff v.val) else 0

def effectivePolynomial {l : ℕ} (m ell : ℕ) (q : Fin l → Poly) : Poly :=
  ∑ i : Fin (2 * ell + 1),
    C (fourierCoeff m q ((i.val : ℤ) - (ell : ℤ))) * X ^ i.val

def reciprocalConj (z : ℂ) : ℂ := (star z)⁻¹
def insideRoots (p : Poly) : Multiset ℂ := by
  classical
  exact p.roots.filter (fun z => ‖z‖ < 1)
def rootProduct (s : Multiset ℂ) : Poly := (s.map (fun z => X - C z)).prod

def directionSum {n k : ℕ} (R : Fin k → Square n) (c : Fin k → ℂ) : Square n :=
  ∑ j, c j • R j

def gradient {n k : ℕ} (T : Square n) (R : Fin k → Square n) (x : H n) : H k :=
  WithLp.toLp 2 (fun j => inner ℂ (euclideanLin T x) (euclideanLin (R j) x))
def gradientImage {n k : ℕ} (T : Square n) (R : Fin k → Square n) : Set (H k) :=
  gradient T R '' unitMaximal T

def basisVector {k : ℕ} (j : Fin k) : H k :=
  WithLp.toLp 2 (fun i => if i = j then 1 else 0)
def separatorCoefficients {k : ℕ} (ell : H k →L[ℝ] ℝ) (j : Fin k) : ℂ :=
  (ell (basisVector j) : ℂ) - Complex.I * (ell (Complex.I • basisVector j) : ℂ)

def descentForm {n : ℕ} (T D : Square n) (x : H n) : ℝ :=
  (inner ℂ (euclideanLin T x) (euclideanLin D x)).re
def descentComplement {n : ℕ} (T D : Square n) (γ : ℝ) : Set (H n) :=
  {x | x ∈ unitSphere n ∧ descentForm T D x ≤ γ / 2}
def descentL {n : ℕ} (D : Square n) : ℝ := operatorNorm D ^ 2
def descentC {n : ℕ} (T D : Square n) : ℝ :=
  2 * operatorNorm T * operatorNorm D + descentL D
def emptyStep {n : ℕ} (D : Square n) (γ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * min 1 (γ / (2 * (descentL D + 1)))
def gapStep {n : ℕ} (T D : Square n) (γ β : ℝ) : ℝ :=
  (1 / 2 : ℝ) * min 1
    (min (γ / (2 * (descentL D + 1))) (β / (2 * (descentC T D + 1))))

def affineResidual {n k : ℕ} (Y : Square n) (R : Fin k → Square n)
    (c : Fin k → ℂ) : Square n := Y - directionSum R c
def affineIdeal {n k : ℕ} (Y : Square n) (R : Fin k → Square n) : ℝ :=
  sInf (Set.range (fun c => operatorNorm (affineResidual Y R c)))
def affineInner {n k : ℕ} (Y : Square n) (R : Fin k → Square n) (x : H n) : ℝ :=
  sInf (Set.range (fun c => ‖euclideanLin (affineResidual Y R c) x‖))
def affineWorst {n k : ℕ} (Y : Square n) (R : Fin k → Square n) : ℝ :=
  sSup (affineInner Y R '' unitSphere n)

def upperShift (n : ℕ) : Square n :=
  fun i j => if j.val = i.val + 1 then 1 else 0
def jordan (n : ℕ) (lam : ℂ) : Square n := lam • 1 + upperShift n
def lowerJordan (n : ℕ) (lam : ℂ) : Square n := lam • 1 + shift n
def reversal (n : ℕ) : Square n := fun i j => if j = i.rev then 1 else 0
def reverseVector {n : ℕ} (x : H n) : H n := WithLp.toLp 2 (fun i => x i.rev)
def polyEval {n : ℕ} (p : Poly) (A : Square n) : Square n := Polynomial.aeval A p
def jordanDirections (n k : ℕ) (lam : ℂ) (j : Fin k) : Square n :=
  lowerJordan n lam ^ (j.val + 1)
def Admissible (k : ℕ) (p : Poly) : Prop := DegreeLE p k ∧ p.eval 0 = 1

def gmresInner {n : ℕ} (A : Square n) (k : ℕ) (x : H n) : ℝ :=
  sInf {t : ℝ | ∃ p : Poly, Admissible k p ∧ t = ‖euclideanLin (polyEval p A) x‖}
def idealGMRES {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  sInf {t : ℝ | ∃ p : Poly, Admissible k p ∧ t = operatorNorm (polyEval p A)}
def worstGMRES {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  sSup (gmresInner A k '' unitSphere n)

end
end NLA.IE02

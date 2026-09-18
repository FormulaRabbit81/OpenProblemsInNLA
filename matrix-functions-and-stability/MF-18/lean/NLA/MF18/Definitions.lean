import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
MF-18 full complex model: transparent statement proposal, NOT elaborated/frozen.
No theorem proof is implemented. Two independent statement reviews are required.
Author of the mathematical solution and prospective formalization:
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology. Preserve Guo--Kuo--Lin and Colbrook credit.
-/

noncomputable section
open scoped BigOperators Topology ComplexOrder

namespace NLA.MF18

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Vec (n : ℕ) := Fin n → ℂ
abbrev CPoly := Polynomial ℂ

def regularizedA {n : ℕ} (C D : Mat n) (η : ℝ) : Mat n :=
  C + (Complex.I * (η : ℂ)) • D

/-- This is generally not the adjoint of regularizedA. -/
def regularizedB {n : ℕ} (C D : Mat n) (η : ℝ) : Mat n :=
  C.conjTranspose + (Complex.I * (η : ℂ)) • D.conjTranspose

def regularizedQ {n : ℕ} (R P : Mat n) (η : ℝ) : Mat n :=
  R + (Complex.I * (η : ℂ)) • P

def matrixPolynomial {n : ℕ} (A B Q : Mat n) : Matrix (Fin n) (Fin n) CPoly :=
  fun i j => Polynomial.C (B i j) * Polynomial.X ^ 2 -
    Polynomial.C (Q i j) * Polynomial.X + Polynomial.C (A i j)

def scalarPencil {n : ℕ} (A B Q : Mat n) : CPoly :=
  (matrixPolynomial A B Q).det

def pencilValue {n : ℕ} (A B Q : Mat n) (lam : ℂ) : Mat n :=
  (lam ^ 2) • B - lam • Q + A

def unregularizedPolynomial {n : ℕ} (C R : Mat n) : CPoly :=
  scalarPencil C C.conjTranspose R

def regularizedPolynomial {n : ℕ} (C D R P : Mat n) (η : ℝ) : CPoly :=
  scalarPencil (regularizedA C D η) (regularizedB C D η) (regularizedQ R P η)

def homotopyPolynomial {n : ℕ} (C D R P : Mat n) (η t : ℝ) : CPoly :=
  scalarPencil ((t : ℂ) • regularizedA C D η)
    ((t : ℂ) • regularizedB C D η)
    ((t : ℂ) • R + (Complex.I * (η : ℂ)) • P)

def CirclePositive {n : ℕ} (P D : Mat n) : Prop :=
  ∀ lam : ℂ, ‖lam‖ = 1 → (P + lam • D.conjTranspose + lam⁻¹ • D).PosDef

def StrictStable {n : ℕ} (S : Mat n) : Prop :=
  ∀ lam : ℂ, S.charpoly.IsRoot lam → ‖lam‖ < 1

def WeakStable {n : ℕ} (S : Mat n) : Prop :=
  ∀ lam : ℂ, S.charpoly.IsRoot lam → ‖lam‖ ≤ 1

def IsStabilizingSolution {n : ℕ} (C D R P : Mat n) (η : ℝ) (X : Mat n) : Prop :=
  X.det ≠ 0 ∧
  X + regularizedB C D η * X⁻¹ * regularizedA C D η = regularizedQ R P η ∧
  StrictStable (X⁻¹ * regularizedA C D η)

def diskRootCount (p : CPoly) : ℕ := by
  classical
  exact (p.roots.filter (fun lam => ‖lam‖ < 1)).card

def circleRootCount (p : CPoly) : ℕ := by
  classical
  exact (p.roots.filter (fun lam => ‖lam‖ = 1)).card

def rightHalfPlaneRootCount (p : CPoly) : ℕ := by
  classical
  exact (p.roots.filter (fun z => 0 < z.re)).card

def SimpleCircleRoots (p : CPoly) : Prop :=
  ∀ lam : ℂ, ‖lam‖ = 1 → p.IsRoot lam → p.rootMultiplicity lam = 1

def CoeffContinuousOn (p : ℝ → CPoly) (s : Set ℝ) : Prop :=
  ∀ j : ℕ, ContinuousOn (fun t => (p t).coeff j) s

/-- Homogenization keeps grade N even if p has lower actual degree. -/
def cayleyPolynomial (N : ℕ) (p : CPoly) : CPoly :=
  ∑ j ∈ Finset.range (N + 1), Polynomial.C (p.coeff j) *
    (Polynomial.X - 1) ^ j * (Polynomial.X + 1) ^ (N - j)

def monicCayleyPolynomial (N : ℕ) (p : CPoly) : CPoly :=
  Polynomial.C ((p.eval 1)⁻¹) * cayleyPolynomial N p

def complementaryPolynomial {n : ℕ} (B X : Mat n) : CPoly :=
  Matrix.det (fun i j => Polynomial.C ((B * X⁻¹) i j) * Polynomial.X -
    Polynomial.C ((1 : Mat n) i j))

def hermitianImaginaryPart {n : ℕ} (X : Mat n) : Mat n :=
  ((2 * Complex.I : ℂ)⁻¹) • (X - X.conjTranspose)

def pairing {n : ℕ} (H : Mat n) (v w : Vec n) : ℂ :=
  ∑ i : Fin n, star (v i) * (H.mulVec w) i

def stableSubspace {n : ℕ} (S : Mat n) : Submodule ℂ (Vec n) :=
  ⨆ (lam : ℂ), ⨆ (_ : ‖lam‖ < 1), Module.End.maxGenEigenspace S.toLin' lam

/-- Only original model assumptions. No rank/count/selection conclusion is a field.
Uniqueness of the given family is not needed for the stronger theorem. -/
def GreenAssumptions {n : ℕ} (C D R P : Mat n) (X : ℝ → Mat n) (X₀ : Mat n) : Prop :=
  R.IsHermitian ∧ P.IsHermitian ∧ CirclePositive P D ∧
  (∀ η : ℝ, 0 < η → IsStabilizingSolution C D R P η (X η)) ∧
  Filter.Tendsto X (nhdsWithin 0 (Set.Ioi 0)) (nhds X₀) ∧
  X₀.det ≠ 0 ∧ unregularizedPolynomial C R ≠ 0 ∧
  SimpleCircleRoots (unregularizedPolynomial C R)

end NLA.MF18

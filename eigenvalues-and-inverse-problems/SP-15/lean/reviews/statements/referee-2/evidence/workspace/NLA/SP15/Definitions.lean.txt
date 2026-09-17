/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

Concrete definitions only. The source is the canonical SP-15 solution.
The rational submersion point and LU route are an explicit formalization
refinement of its constant-rank argument. No fiber, derivative identity,
positivity, singular-value identity, or rigidity theorem is assumed here.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Topology

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Parameters := Fin 10 → ℝ
abbrev Coefficients := Fin 9 → ℝ
abbrev BlockIndex := Fin 3 ⊕ (Fin 3 ⊕ Fin 3)
abbrev BlockSquare := Matrix BlockIndex BlockIndex ℂ

/-- Exact numerical data, in order p₁,p₂,p₃,q₁,q₂,q₃,a,b,c,d. -/
def basePoint : Parameters := ![1, 2, 3, 4, 4, 4, 1, 1, 1, 1]
def boxRadius : ℝ := 1 / 16
def parameterBox : Set Parameters := {x | ∀ i, |x i - basePoint i| < boxRadius}
def pCoordinates (x : Parameters) : Fin 3 → ℝ := ![x 0, x 1, x 2]

def pMatrix (x : Parameters) : Square 3 :=
  Matrix.diagonal (fun i => (pCoordinates x i : ℂ))

def qMatrix (x : Parameters) : Square 3 :=
  !![(x 3 : ℂ), (x 6 : ℂ), (x 7 : ℂ);
      (x 6 : ℂ), (x 4 : ℂ), (x 8 : ℂ) + Complex.I * (x 9 : ℂ);
      (x 7 : ℂ), (x 8 : ℂ) - Complex.I * (x 9 : ℂ), (x 5 : ℂ)]

/-- Genuine positive-functional-calculus roots, with properties left to proof. -/
def pRoot (x : Parameters) : Square 3 := CFC.sqrt (pMatrix x)
def qRoot (x : Parameters) : Square 3 := CFC.sqrt (qMatrix x)

def blockEquiv : BlockIndex ≃ Fin 9 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3)) (finSumFinEquiv (m := 3) (n := 3))).trans
    (finSumFinEquiv (m := 3) (n := 6))

/-- The actual nilpotent three-block construction before reindexing. -/
def blockMatrix (x : Parameters) : BlockSquare :=
  Matrix.fromBlocks (0 : Square 3)
    (Matrix.fromCols (pRoot x) (0 : Square 3))
    (Matrix.fromRows (0 : Square 3) (0 : Square 3))
    (Matrix.fromBlocks (0 : Square 3) (qRoot x) (0 : Square 3) (0 : Square 3))

def constructedMatrix (x : Parameters) : Square 9 :=
  Matrix.reindex blockEquiv blockEquiv (blockMatrix x)

def diagonalBlocks (U V W : Square 3) : Square 9 :=
  Matrix.reindex blockEquiv blockEquiv
    (Matrix.fromBlocks U
      (Matrix.fromCols (0 : Square 3) (0 : Square 3))
      (Matrix.fromRows (0 : Square 3) (0 : Square 3))
      (Matrix.fromBlocks V (0 : Square 3) (0 : Square 3) W))

/-- The determinant whose exact nine coefficients determine the shifted data. -/
def coefficientDeterminant (x : Parameters) (u s : ℂ) : ℂ :=
  Matrix.det (u • (1 : Square 3) + s • (pMatrix x + qMatrix x) + pMatrix x * qMatrix x)

/-- Nine explicitly collected real polynomials. Their determinant meaning and
    actual derivative are independent proof obligations. -/
def coefficients (x : Parameters) : Coefficients :=
  let p₁ := x 0; let p₂ := x 1; let p₃ := x 2
  let q₁ := x 3; let q₂ := x 4; let q₃ := x 5
  let a := x 6; let b := x 7; let c := x 8; let d := x 9
  let r₁ := p₁ + q₁; let r₂ := p₂ + q₂; let r₃ := p₃ + q₃
  let t₁ := p₁ * q₁; let t₂ := p₂ * q₂; let t₃ := p₃ * q₃
  let e := c ^ 2 + d ^ 2
  ![t₁ * t₂ * t₃ - e * p₂ * p₃ * t₁ - b ^ 2 * p₁ * p₃ * t₂ -
      a ^ 2 * p₁ * p₂ * t₃ + 2 * a * b * c * p₁ * p₂ * p₃,
    t₁ * t₂ + t₁ * t₃ + t₂ * t₃ - e * p₂ * p₃ - b ^ 2 * p₁ * p₃ -
      a ^ 2 * p₁ * p₂,
    r₁ * t₂ * t₃ + t₁ * r₂ * t₃ + t₁ * t₂ * r₃ -
      e * (p₂ * p₃ * r₁ + (p₂ + p₃) * t₁) -
      b ^ 2 * (p₁ * p₃ * r₂ + (p₁ + p₃) * t₂) -
      a ^ 2 * (p₁ * p₂ * r₃ + (p₁ + p₂) * t₃) +
      2 * a * b * c * (p₁ * p₂ + p₁ * p₃ + p₂ * p₃),
    t₁ + t₂ + t₃,
    r₁ * t₂ + t₁ * r₂ + r₁ * t₃ + t₁ * r₃ + r₂ * t₃ + t₂ * r₃ -
      e * (p₂ + p₃) - b ^ 2 * (p₁ + p₃) - a ^ 2 * (p₁ + p₂),
    r₁ * r₂ * t₃ + r₁ * t₂ * r₃ + t₁ * r₂ * r₃ -
      e * ((p₂ + p₃) * r₁ + t₁) -
      b ^ 2 * ((p₁ + p₃) * r₂ + t₂) -
      a ^ 2 * ((p₁ + p₂) * r₃ + t₃) + 2 * a * b * c * (p₁ + p₂ + p₃),
    r₁ + r₂ + r₃,
    r₁ * r₂ + r₁ * r₃ + r₂ * r₃ - e - b ^ 2 - a ^ 2,
    r₁ * r₂ * r₃ - e * r₁ - b ^ 2 * r₂ - a ^ 2 * r₃ + 2 * a * b * c]

def coefficientMonomials (u s : ℂ) : Fin 9 → ℂ :=
  ![1, u, s, u ^ 2, u * s, s ^ 2, u ^ 2 * s, u * s ^ 2, s ^ 3]

def coefficientBaseValue : Coefficients := ![300, 159, 814, 24, 263, 697, 18, 103, 189]

/-- Candidate numerical Jacobian data, not a derivative by definition. -/
def jacobian : Matrix (Fin 9) (Fin 10) ℝ :=
  !![300, 150, 100, 84, 90, 90, -36, -36, -36, -48;
      75, 57, 43, 20, 32, 36, -4, -6, -12, -12;
      514, 332, 238, 202, 213, 213, -78, -78, -78, -100;
      4, 4, 4, 1, 2, 3, 0, 0, 0, 0;
      70, 61, 53, 33, 40, 45, -6, -8, -10, -10;
      267, 205, 163, 158, 152, 148, -54, -52, -46, -58;
      1, 1, 1, 1, 1, 1, 0, 0, 0, 0;
      13, 12, 11, 13, 12, 11, -2, -2, -2, -2;
      40, 34, 29, 40, 34, 29, -12, -10, -8, -10]

def jacobianMinor : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => jacobian i j.castSucc

/-- Exact rational LU data; all reconstruction/triangular facts are goals. -/
def lowerCertificate : Matrix (Fin 9) (Fin 9) ℝ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
      1/4, 1, 0, 0, 0, 0, 0, 0, 0;
      257/150, 50/13, 1, 0, 0, 0, 0, 0, 0;
      1/75, 4/39, -8/25, 1, 0, 0, 0, 0, 0;
      7/30, 4/3, -221/100, 568463/74246, 1, 0, 0, 0, 0;
      89/100, 11/3, -78/25, 525218/37123, 1218104/345081, 1, 0, 0, 0;
      1/300, 1/39, -2/25, 10687/37123, 3196/31371, -407/16366, 1, 0, 0;
      13/300, 11/39, -31/50, 90068/37123, 350762/345081, -1217/73647, 198808/37827, 1, 0;
      2/15, 28/39, -107/100, 359171/74246, 799091/345081, 79979/147294, 216673/37827, 8825/2093, 1]

def upperCertificate : Matrix (Fin 9) (Fin 9) ℝ :=
  !![300, 150, 100, 84, 90, 90, -36, -36, -36;
      0, 39/2, 18, -1, 19/2, 27/2, 5, 3, -3;
      0, 0, -100/39, 20126/325, 1447/65, 447/65, -11554/325, -9054/325, -1554/325;
      0, 0, 0, 37123/1875, 2606/375, 327/125, -21392/1875, -5464/625, -464/625;
      0, 0, 0, 0, 345081/148492, 173535/148492, 335549/74246, 131327/74246, -184355/74246;
      0, 0, 0, 0, 0, -147294/115027, -1983818/345081, -149846/345081, 479654/345081;
      0, 0, 0, 0, 0, 0, -1401/8183, 1147/8183, 369/1169;
      0, 0, 0, 0, 0, 0, 0, 4186/37827, 1648/12609;
      0, 0, 0, 0, 0, 0, 0, 0, 136/2093]

def coefficientDerivative : Parameters →L[ℝ] Coefficients :=
  jacobian.mulVecLin.toContinuousLinearMap

/-- The tenth coordinate of the genuine augmented map is the original d. -/
def augmented (x : Parameters) : Parameters :=
  Fin.lastCases (x 9) (coefficients x)

def augmentedJacobian : Matrix (Fin 10) (Fin 10) ℝ :=
  Fin.lastCases (fun j => if j = 9 then 1 else 0) jacobian

def augmentedDerivative : Parameters →L[ℝ] Parameters :=
  augmentedJacobian.mulVecLin.toContinuousLinearMap

/-- Actual shifted Gram matrix, with no spectral assumptions. -/
def shiftedGram {n : ℕ} (A : Square n) (z : ℂ) : Square n :=
  (A - z • (1 : Square n)).conjTranspose * (A - z • (1 : Square n))

def shiftScalar (z : ℂ) (t : ℝ) : ℝ := t + Complex.normSq z

def schurPivot (x : Parameters) (z : ℂ) (t : ℝ) : Square 3 :=
  ((shiftScalar z t ^ 2 : ℝ) : ℂ) • (1 : Square 3) + (t : ℂ) • pMatrix x

/-- Explicit Gram block expansion. Its equality to the Gram matrix is not
    assumed by this definition; it is an exact algebraic contract. -/
def regularizedGramBlocks (x : Parameters) (z : ℂ) (t : ℝ) : BlockSquare :=
  let s : ℂ := (shiftScalar z t : ℝ)
  Matrix.fromBlocks (s • (1 : Square 3))
    (Matrix.fromCols ((-star z) • pRoot x) (0 : Square 3))
    (Matrix.fromRows ((-z) • (pRoot x).conjTranspose) (0 : Square 3))
    (Matrix.fromBlocks (s • (1 : Square 3) + pMatrix x)
      ((-star z) • qRoot x) ((-z) • (qRoot x).conjTranspose)
      (s • (1 : Square 3) + (qRoot x).conjTranspose * qRoot x))

/-- Mathlib's genuine decreasing Euclidean singular values, zero extended. -/
def singularValue {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues k

/-- The original all-complex-shift, every-ordered-singular-value relation. -/
def SuperIdentical {n : ℕ} (A B : Square n) : Prop :=
  ∀ (z : ℂ) (k : Fin n),
    singularValue (A - z • (1 : Square n)) k.val =
      singularValue (B - z • (1 : Square n)) k.val

/-- Exactly the one-sided unitary condition in the canonical question. -/
def UnitarySimilar {n : ℕ} (A B : Square n) : Prop :=
  ∃ U : Square n, U.conjTranspose * U = 1 ∧ B = U.conjTranspose * A * U

/-- Literal universal finiteness statement from the retained canonical page. -/
def CanonicalFiniteness : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ M : ℕ, 1 ≤ M ∧
    ∀ A : Fin (M + 1) → Square n,
      (∀ i j, SuperIdentical (A i) (A j)) →
        ∃ i j : Fin (M + 1), i < j ∧ UnitarySimilar (A i) (A j)

end
end NLA.SP15

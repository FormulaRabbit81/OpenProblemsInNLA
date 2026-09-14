/-
The concrete Hermitian seed at the beginning of Li's construction.  This file
contains only finite-dimensional exact identities; the later local chart and
probability estimates are intentionally separate.
-/
import NLA.FR05.Definitions
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

private theorem firstCoordinate_ne_secondCoordinate' (d : ℕ) (hd : 2 ≤ d) :
    firstCoordinate d hd ≠ secondCoordinate d hd := by
  simp [firstCoordinate, secondCoordinate]

/-- The constant-one test vector.  It is the conjugated row of `flatFrame`. -/
def allOnesSignal (d : ℕ) : Signal d := fun _ => 1

/-- Li's diagonal seed is Hermitian. -/
theorem qZero_isHermitian (d : ℕ) (hd : 2 ≤ d) :
    (qZero d hd).IsHermitian := by
  rw [qZero, Matrix.isHermitian_diagonal_iff]
  intro k
  rw [isSelfAdjoint_iff]
  by_cases hk₀ : k = firstCoordinate d hd
  · simp [hk₀]
  · by_cases hk₁ : k = secondCoordinate d hd
    · have hne : secondCoordinate d hd ≠ firstCoordinate d hd :=
        Ne.symm (firstCoordinate_ne_secondCoordinate' d hd)
      simp [hk₁, hne]
    · simp [hk₀, hk₁]

/-- Acting on the constant-one vector, the seed produces the difference of
the first two coordinate vectors. -/
theorem qZero_mulVec_allOnes (d : ℕ) (hd : 2 ≤ d) :
    qZero d hd *ᵥ allOnesSignal d =
      standardBasis (firstCoordinate d hd) - standardBasis (secondCoordinate d hd) := by
  funext k
  rw [qZero, Matrix.mulVec_diagonal]
  by_cases hk₀ : k = firstCoordinate d hd
  · subst k
    simp [allOnesSignal, standardBasis,
      firstCoordinate_ne_secondCoordinate' d hd]
  · by_cases hk₁ : k = secondCoordinate d hd
    · subst k
      have hne : secondCoordinate d hd ≠ firstCoordinate d hd :=
        Ne.symm (firstCoordinate_ne_secondCoordinate' d hd)
      simp [allOnesSignal, standardBasis, hne]
    · simp [allOnesSignal, standardBasis, hk₀, hk₁]

/-- The Hermitian seed is invisible to the constant-one row.  This is the
finite exact identity underlying the planted ambiguity before any stability
or distributional estimate is introduced. -/
theorem quadraticForm_qZero_allOnes (d : ℕ) (hd : 2 ≤ d) :
    quadraticForm (qZero d hd) (allOnesSignal d) = 0 := by
  rw [quadraticForm, qZero_mulVec_allOnes]
  simp [allOnesSignal, standardBasis, dotProduct, Finset.sum_sub_distrib]

end NLA.FR05

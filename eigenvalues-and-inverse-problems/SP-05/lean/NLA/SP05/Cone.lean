/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Modulus
import NLA.SP05.Jordan

noncomputable section
open Matrix
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace NLA.SP05

/-- Complexification preserves the actual Kronecker coefficients. -/
theorem complexify_kronecker {n : ℕ} (A B : Mat n) :
    complexify (Matrix.kronecker A B) =
      Matrix.kronecker (complexify A) (complexify B) := by
  ext i j
  simp [complexify, Matrix.kronecker, Matrix.kroneckerMap]

/-- The complexified coefficient matrix acts by the literal complex Jordan equation. -/
theorem complex_jordan_columnVec {n : ℕ} {A B : Mat n}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (X : Matrix (Fin n) (Fin n) ℂ) :
    complexify (jordanMatrix A B) *ᵥ vec X =
      vec (complexify A * X * complexify B + complexify B * X * complexify A) := by
  have hAt : Aᵀ=A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hBt : Bᵀ=B := by simpa only [conjTranspose_eq_transpose_of_trivial] using hB.eq
  rw [jordanMatrix, complexify_add, complexify_kronecker, complexify_kronecker]
  simp only [Matrix.kronecker, add_mulVec, kronecker_mulVec_vec, ← complexify_transpose, hAt, hBt, ← vec_add,
    add_comm]

/-- The exact inverse coefficient action solves the full complex Jordan equation. -/
theorem actual_jordan_inverse_equation {n : ℕ} {A B : Mat n}
    (hA : A.PosDef) (hB : B.PosDef) (X : Matrix (Fin n) (Fin n) ℂ) :
    complexify A * complexMatrixAction (jordanMatrix A B)⁻¹ X * complexify B +
      complexify B * complexMatrixAction (jordanMatrix A B)⁻¹ X * complexify A = X := by
  have hJ := jordan_posDef hA hB
  have hCJ := complexify_posDef hJ
  apply Matrix.vec_inj.mp
  rw [← complex_jordan_columnVec hA.isHermitian hB.isHermitian,
    vec_complexMatrixAction, complexify_inv hJ.isUnit, mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hCJ.isUnit), one_mulVec]

/-- The actual inverse Jordan matrix preserves the entire complex Hermitian PSD cone. -/
theorem actual_jordan_inverse_cone {n : ℕ} {A B : Mat n}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
      (complexMatrixAction (jordanMatrix A B)⁻¹ X).PosSemidef := by
  intro X hX
  exact complex_jordan_solution_posSemidef (complexify_posDef hA) (complexify_posDef hB)
    hX (actual_jordan_inverse_equation hA hB X)

#assert_trust kernel complex_jordan_columnVec
#assert_trust kernel actual_jordan_inverse_equation
#assert_trust kernel actual_jordan_inverse_cone
#print axioms complex_jordan_columnVec
#print axioms actual_jordan_inverse_equation
#print axioms actual_jordan_inverse_cone
end NLA.SP05

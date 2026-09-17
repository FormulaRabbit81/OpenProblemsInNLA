/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

Explicit nine-block algebra on the frozen nested Sum index. These helpers
expand only the three block products, never the scalar entries of the blocks.
-/
import NLA.SP15.Numerical
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped Matrix

def tripleBlock (A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ : Square 3) : BlockSquare :=
  Matrix.fromBlocks A₁₁ (Matrix.fromCols A₁₂ A₁₃) (Matrix.fromRows A₂₁ A₃₁)
    (Matrix.fromBlocks A₂₂ A₂₃ A₃₂ A₃₃)

theorem triple_decomposition (U : BlockSquare) :
    U = tripleBlock
      (U.submatrix Sum.inl Sum.inl)
      (U.submatrix Sum.inl (Sum.inr ∘ Sum.inl))
      (U.submatrix Sum.inl (Sum.inr ∘ Sum.inr))
      (U.submatrix (Sum.inr ∘ Sum.inl) Sum.inl)
      (U.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      (U.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr))
      (U.submatrix (Sum.inr ∘ Sum.inr) Sum.inl)
      (U.submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inl))
      (U.submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inr)) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> rfl

theorem triple_one : tripleBlock 1 0 0 0 1 0 0 0 1 = (1 : BlockSquare) := by
  simp only [tripleBlock, Matrix.fromCols_zero, Matrix.fromRows_zero, Matrix.fromBlocks_one]

theorem triple_eq_iff
    (A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃
     B₁₁ B₁₂ B₁₃ B₂₁ B₂₂ B₂₃ B₃₁ B₃₂ B₃₃ : Square 3) :
    tripleBlock A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ =
        tripleBlock B₁₁ B₁₂ B₁₃ B₂₁ B₂₂ B₂₃ B₃₁ B₃₂ B₃₃ ↔
      A₁₁ = B₁₁ ∧ (A₁₂ = B₁₂ ∧ A₁₃ = B₁₃) ∧
      (A₂₁ = B₂₁ ∧ A₃₁ = B₃₁) ∧
      A₂₂ = B₂₂ ∧ A₂₃ = B₂₃ ∧ A₃₂ = B₃₂ ∧ A₃₃ = B₃₃ := by
  simp only [tripleBlock, Matrix.fromBlocks_inj, Matrix.fromCols_ext_iff,
    Matrix.fromRows_ext_iff]

theorem triple_conjTranspose (A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ : Square 3) :
    (tripleBlock A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃).conjTranspose =
      tripleBlock A₁₁.conjTranspose A₂₁.conjTranspose A₃₁.conjTranspose
        A₁₂.conjTranspose A₂₂.conjTranspose A₃₂.conjTranspose
        A₁₃.conjTranspose A₂₃.conjTranspose A₃₃.conjTranspose := by
  simp only [tripleBlock, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose]

theorem triple_mul
    (A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃
     B₁₁ B₁₂ B₁₃ B₂₁ B₂₂ B₂₃ B₃₁ B₃₂ B₃₃ : Square 3) :
    tripleBlock A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ *
        tripleBlock B₁₁ B₁₂ B₁₃ B₂₁ B₂₂ B₂₃ B₃₁ B₃₂ B₃₃ =
      tripleBlock
        (A₁₁ * B₁₁ + A₁₂ * B₂₁ + A₁₃ * B₃₁)
        (A₁₁ * B₁₂ + A₁₂ * B₂₂ + A₁₃ * B₃₂)
        (A₁₁ * B₁₃ + A₁₂ * B₂₃ + A₁₃ * B₃₃)
        (A₂₁ * B₁₁ + A₂₂ * B₂₁ + A₂₃ * B₃₁)
        (A₂₁ * B₁₂ + A₂₂ * B₂₂ + A₂₃ * B₃₂)
        (A₂₁ * B₁₃ + A₂₂ * B₂₃ + A₂₃ * B₃₃)
        (A₃₁ * B₁₁ + A₃₂ * B₂₁ + A₃₃ * B₃₁)
        (A₃₁ * B₁₂ + A₃₂ * B₂₂ + A₃₃ * B₃₂)
        (A₃₁ * B₁₃ + A₃₂ * B₂₃ + A₃₃ * B₃₃) := by
  simp only [tripleBlock, Matrix.fromBlocks_multiply, Matrix.fromCols_mul_fromRows,
    Matrix.fromRows_mul, Matrix.mul_fromCols,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromBlocks_mul_fromRows]
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [Matrix.add_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]
  all_goals abel

#print axioms triple_mul
#assert_trust kernel triple_mul

end
end NLA.SP15

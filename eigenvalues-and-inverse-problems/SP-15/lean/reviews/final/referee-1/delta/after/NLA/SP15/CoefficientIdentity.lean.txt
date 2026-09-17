/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

The actual 3×3 determinant is factored before coefficient collection.
All parameters and both complex scalar variables remain arbitrary.
-/
import NLA.SP15.Numerical
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix ComplexConjugate

private theorem weighted_three_det (D₁ D₂ D₃ S₁ S₂ S₃ a b z w : ℂ) :
    Matrix.det !![D₁, S₁ * a, S₁ * b;
      S₂ * a, D₂, S₂ * z;
      S₃ * b, S₃ * w, D₃] =
      D₁ * D₂ * D₃ - (z * w) * S₂ * S₃ * D₁ -
        b ^ 2 * S₁ * S₃ * D₂ - a ^ 2 * S₁ * S₂ * D₃ +
        a * b * (z + w) * S₁ * S₂ * S₃ := by
  rw [Matrix.det_fin_three]
  -- Each displayed entry is definitionally the corresponding literal matrix lookup.
  change D₁ * D₂ * D₃ - D₁ * (S₂ * z) * (S₃ * w) -
      (S₁ * a) * (S₂ * a) * D₃ + (S₁ * a) * (S₂ * z) * (S₃ * b) +
      (S₁ * b) * (S₂ * a) * (S₃ * w) - (S₁ * b) * D₂ * (S₃ * b) = _
  ring

private theorem real_conjugate_pair (c d : ℝ) :
    ((c : ℂ) + Complex.I * (d : ℂ)) * ((c : ℂ) - Complex.I * (d : ℂ)) =
      ((c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
  calc
    _ = ((c : ℂ) + Complex.I * (d : ℂ)) *
        conj ((c : ℂ) + Complex.I * (d : ℂ)) := by simp [sub_eq_add_neg]
    _ = (Complex.normSq ((c : ℂ) + Complex.I * (d : ℂ)) : ℂ) :=
      Complex.mul_conj _
    _ = _ := by rw [mul_comm Complex.I (d : ℂ), Complex.normSq_add_mul_I]

theorem coefficient_determinant_identity (x : Parameters) (u s : ℂ) :
    coefficientDeterminant x u s =
      u ^ 3 + ∑ i : Fin 9, (coefficients x i : ℂ) * coefficientMonomials u s i := by
  let D₁ := u + s * ((x 0 : ℂ) + (x 3 : ℂ)) + (x 0 : ℂ) * (x 3 : ℂ)
  let D₂ := u + s * ((x 1 : ℂ) + (x 4 : ℂ)) + (x 1 : ℂ) * (x 4 : ℂ)
  let D₃ := u + s * ((x 2 : ℂ) + (x 5 : ℂ)) + (x 2 : ℂ) * (x 5 : ℂ)
  let S₁ := s + (x 0 : ℂ)
  let S₂ := s + (x 1 : ℂ)
  let S₃ := s + (x 2 : ℂ)
  have hmatrix : u • (1 : Square 3) + s • (pMatrix x + qMatrix x) + pMatrix x * qMatrix x =
      !![D₁, S₁ * (x 6 : ℂ), S₁ * (x 7 : ℂ);
        S₂ * (x 6 : ℂ), D₂, S₂ * ((x 8 : ℂ) + Complex.I * (x 9 : ℂ));
        S₃ * (x 7 : ℂ), S₃ * ((x 8 : ℂ) - Complex.I * (x 9 : ℂ)), D₃] := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, pMatrix,
      Matrix.diagonal_mul]
    -- The nine cases expose literal matrix-notation entries and the local D/S abbreviations.
    fin_cases i <;> fin_cases j
    · change u * 1 + s * ((x 0 : ℂ) + (x 3 : ℂ)) + (x 0 : ℂ) * (x 3 : ℂ) = D₁
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 0 + s * (0 + (x 6 : ℂ)) + (x 0 : ℂ) * (x 6 : ℂ) = S₁ * (x 6 : ℂ)
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 0 + s * (0 + (x 7 : ℂ)) + (x 0 : ℂ) * (x 7 : ℂ) = S₁ * (x 7 : ℂ)
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 0 + s * (0 + (x 6 : ℂ)) + (x 1 : ℂ) * (x 6 : ℂ) = S₂ * (x 6 : ℂ)
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 1 + s * ((x 1 : ℂ) + (x 4 : ℂ)) + (x 1 : ℂ) * (x 4 : ℂ) = D₂
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 0 + s * (0 + ((x 8 : ℂ) + Complex.I * (x 9 : ℂ))) +
        (x 1 : ℂ) * ((x 8 : ℂ) + Complex.I * (x 9 : ℂ)) = S₂ * ((x 8 : ℂ) + Complex.I * (x 9 : ℂ))
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 0 + s * (0 + (x 7 : ℂ)) + (x 2 : ℂ) * (x 7 : ℂ) = S₃ * (x 7 : ℂ)
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 0 + s * (0 + ((x 8 : ℂ) - Complex.I * (x 9 : ℂ))) +
        (x 2 : ℂ) * ((x 8 : ℂ) - Complex.I * (x 9 : ℂ)) = S₃ * ((x 8 : ℂ) - Complex.I * (x 9 : ℂ))
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
    · change u * 1 + s * ((x 2 : ℂ) + (x 5 : ℂ)) + (x 2 : ℂ) * (x 5 : ℂ) = D₃
      dsimp only [D₁, D₂, D₃, S₁, S₂, S₃]
      ring
  unfold coefficientDeterminant
  rw [hmatrix, weighted_three_det, real_conjugate_pair]
  -- Only the nine coefficient terms remain; no larger determinant is expanded.
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  let p₁ := x 0; let p₂ := x 1; let p₃ := x 2
  let q₁ := x 3; let q₂ := x 4; let q₃ := x 5
  let a := x 6; let b := x 7; let c := x 8; let d := x 9
  let r₁ := p₁ + q₁; let r₂ := p₂ + q₂; let r₃ := p₃ + q₃
  let t₁ := p₁ * q₁; let t₂ := p₂ * q₂; let t₃ := p₃ * q₃
  let e := c ^ 2 + d ^ 2
  -- Typed conversion checks every coefficient and monomial lookup directly.
  change _ = u ^ 3 + (((t₁ * t₂ * t₃ - e * p₂ * p₃ * t₁ - b ^ 2 * p₁ * p₃ * t₂ - a ^ 2 * p₁ * p₂ *
    t₃ + 2 * a * b * c * p₁ * p₂ * p₃ : ℝ) : ℂ) * (1) + (((t₁ * t₂ + t₁ * t₃ + t₂ * t₃ - e * p₂ * p₃ -
    b ^ 2 * p₁ * p₃ - a ^ 2 * p₁ * p₂ : ℝ) : ℂ) * (u) + (((r₁ * t₂ * t₃ + t₁ * r₂ * t₃ + t₁ * t₂ * r₃
    - e * (p₂ * p₃ * r₁ + (p₂ + p₃) * t₁) - b ^ 2 * (p₁ * p₃ * r₂ + (p₁ + p₃) * t₂) - a ^ 2 * (p₁ * p₂
    * r₃ + (p₁ + p₂) * t₃) + 2 * a * b * c * (p₁ * p₂ + p₁ * p₃ + p₂ * p₃) : ℝ) : ℂ) * (s) + (((t₁ +
    t₂ + t₃ : ℝ) : ℂ) * (u ^ 2) + (((r₁ * t₂ + t₁ * r₂ + r₁ * t₃ + t₁ * r₃ + r₂ * t₃ + t₂ * r₃ - e *
    (p₂ + p₃) - b ^ 2 * (p₁ + p₃) - a ^ 2 * (p₁ + p₂) : ℝ) : ℂ) * (u * s) + (((r₁ * r₂ * t₃ + r₁ * t₂
    * r₃ + t₁ * r₂ * r₃ - e * ((p₂ + p₃) * r₁ + t₁) - b ^ 2 * ((p₁ + p₃) * r₂ + t₂) - a ^ 2 * ((p₁ +
    p₂) * r₃ + t₃) + 2 * a * b * c * (p₁ + p₂ + p₃) : ℝ) : ℂ) * (s ^ 2) + (((r₁ + r₂ + r₃ : ℝ) : ℂ) *
    (u ^ 2 * s) + (((r₁ * r₂ + r₁ * r₃ + r₂ * r₃ - e - b ^ 2 - a ^ 2 : ℝ) : ℂ) * (u * s ^ 2) + (((r₁ *
    r₂ * r₃ - e * r₁ - b ^ 2 * r₂ - a ^ 2 * r₃ + 2 * a * b * c : ℝ) : ℂ) * (s ^ 3) + 0)))))))))
  dsimp only [D₁, D₂, D₃, S₁, S₂, S₃, p₁, p₂, p₃, q₁, q₂, q₃, a, b, c, d,
    r₁, r₂, r₃, t₁, t₂, t₃, e]
  push_cast
  ring

#print axioms coefficient_determinant_identity
#assert_trust kernel coefficient_determinant_identity

end
end NLA.SP15

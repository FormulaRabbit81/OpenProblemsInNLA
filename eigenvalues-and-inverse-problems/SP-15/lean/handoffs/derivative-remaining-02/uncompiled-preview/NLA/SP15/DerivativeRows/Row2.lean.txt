/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

The displayed scalar identity is the actual derivative map applied to an
arbitrary perturbation vector. Its ten entries are checked by the kernel.
-/
import NLA.SP15.DerivativeRows.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section

theorem coefficient_strict_derivative_row_2 :
    HasStrictFDerivAt (fun x : Parameters => coefficients x 2)
      ((ContinuousLinearMap.proj (2 : Fin 9) : Coefficients →L[ℝ] ℝ).comp
        coefficientDerivative) basePoint := by
  have h (i : Fin 10) := hasStrictFDerivAt_apply (𝕜 := ℝ) i basePoint
  have hr₁ := ((h 0).add (h 3))
  have hr₂ := ((h 1).add (h 4))
  have hr₃ := ((h 2).add (h 5))
  have ht₁ := ((h 0).mul (h 3))
  have ht₂ := ((h 1).mul (h 4))
  have ht₃ := ((h 2).mul (h 5))
  have he := (((h 8).pow 2).add ((h 9).pow 2))
  have hc := ((((((((hr₁.mul ht₂).mul ht₃).add ((ht₁.mul hr₂).mul ht₃)).add ((ht₁.mul ht₂).mul hr₃)).sub
    (he.mul ((((h 1).mul (h 2)).mul hr₁).add (((h 1).add (h 2)).mul ht₁)))).sub (((h 7).pow 2).mul ((((h
    0).mul (h 2)).mul hr₂).add (((h 0).add (h 2)).mul ht₂)))).sub (((h 6).pow 2).mul ((((h 0).mul (h
    1)).mul hr₃).add (((h 0).add (h 1)).mul ht₃)))).add (((((h 6).const_mul 2).mul (h 7)).mul (h 8)).mul
    ((((h 0).mul (h 1)).add ((h 0).mul (h 2))).add ((h 1).mul (h 2)))))
  refine hc.congr_fderiv ?_
  ext v
  rw [coefficient_derivative_row_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  let r₁ : ℝ := (1 + 4)
  let dr₁ : ℝ := (v 0 + v 3)
  let r₂ : ℝ := (2 + 4)
  let dr₂ : ℝ := (v 1 + v 4)
  let r₃ : ℝ := (3 + 4)
  let dr₃ : ℝ := (v 2 + v 5)
  let t₁ : ℝ := (1 * 4)
  let dt₁ : ℝ := (1 * (v 3) + 4 * (v 0))
  let t₂ : ℝ := (2 * 4)
  let dt₂ : ℝ := (2 * (v 4) + 4 * (v 1))
  let t₃ : ℝ := (3 * 4)
  let dt₃ : ℝ := (3 * (v 5) + 4 * (v 2))
  let e : ℝ := ((1 ^ 2) + (1 ^ 2))
  let de : ℝ := (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 8)) + ((2 • ((1 : ℝ) ^ (2 - 1))) * (v 9)))
  change ((((((((r₁ * t₂) * (dt₃) + t₃ * ((r₁ * (dt₂) + t₂ * (dr₁)))) + ((t₁ * r₂) * (dt₃) + t₃ * ((t₁ *
    (dr₂) + r₂ * (dt₁))))) + ((t₁ * t₂) * (dr₃) + r₃ * ((t₁ * (dt₂) + t₂ * (dt₁))))) - (e * ((((2 * 3) *
    (dr₁) + r₁ * ((2 * (v 2) + 3 * (v 1)))) + ((2 + 3) * (dt₁) + t₁ * ((v 1 + v 2))))) + (((2 * 3) * r₁)
    + ((2 + 3) * t₁)) * (de))) - ((1 ^ 2) * ((((1 * 3) * (dr₂) + r₂ * ((1 * (v 2) + 3 * (v 0)))) + ((1 +
    3) * (dt₂) + t₂ * ((v 0 + v 2))))) + (((1 * 3) * r₂) + ((1 + 3) * t₂)) * (((2 • ((1 : ℝ) ^ (2 - 1)))
    * (v 7))))) - ((1 ^ 2) * ((((1 * 2) * (dr₃) + r₃ * ((1 * (v 1) + 2 * (v 0)))) + ((1 + 2) * (dt₃) +
    t₃ * ((v 0 + v 1))))) + (((1 * 2) * r₃) + ((1 + 2) * t₃)) * (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 6)))))
    + ((((2 * 1) * 1) * 1) * ((((1 * (v 1) + 2 * (v 0)) + (1 * (v 2) + 3 * (v 0))) + (2 * (v 2) + 3 * (v
    1)))) + (((1 * 2) + (1 * 3)) + (2 * 3)) * ((((2 * 1) * 1) * (v 8) + 1 * (((2 * 1) * (v 7) + 1 * ((2
    * (v 6))))))))) = (514 * v 0 + (332 * v 1 + (238 * v 2 + (202 * v 3 + (213 * v 4 + (213 * v 5 + (-78
    * v 6 + (-78 * v 7 + (-78 * v 8 + (-100 * v 9 + 0))))))))))
  dsimp only [r₁, dr₁, r₂, dr₂, r₃, dr₃, t₁, dt₁, t₂, dt₂, t₃, dt₃, e, de]
  simp only [nsmul_eq_mul]
  ring

#print axioms coefficient_strict_derivative_row_2
#assert_trust kernel coefficient_strict_derivative_row_2

end
end NLA.SP15

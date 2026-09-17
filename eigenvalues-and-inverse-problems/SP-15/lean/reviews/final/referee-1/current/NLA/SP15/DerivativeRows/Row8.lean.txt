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

theorem coefficient_strict_derivative_row_8 :
    HasStrictFDerivAt (fun x : Parameters => coefficients x 8)
      ((ContinuousLinearMap.proj (8 : Fin 9) : Coefficients →L[ℝ] ℝ).comp
        coefficientDerivative) basePoint := by
  have h (i : Fin 10) := hasStrictFDerivAt_apply (𝕜 := ℝ) i basePoint
  have hr₁ := ((h 0).add (h 3))
  have hr₂ := ((h 1).add (h 4))
  have hr₃ := ((h 2).add (h 5))
  have he := (((h 8).pow 2).add ((h 9).pow 2))
  have hc := ((((((hr₁.mul hr₂).mul hr₃).sub (he.mul hr₁)).sub (((h 7).pow 2).mul hr₂)).sub (((h 6).pow
    2).mul hr₃)).add ((((h 6).const_mul 2).mul (h 7)).mul (h 8)))
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
  let e : ℝ := ((1 ^ 2) + (1 ^ 2))
  let de : ℝ := (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 8)) + ((2 • ((1 : ℝ) ^ (2 - 1))) * (v 9)))
  change ((((((r₁ * r₂) * (dr₃) + r₃ * ((r₁ * (dr₂) + r₂ * (dr₁)))) - (e * (dr₁) + r₁ * (de))) - ((1 ^
    2) * (dr₂) + r₂ * (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 7))))) - ((1 ^ 2) * (dr₃) + r₃ * (((2 • ((1 : ℝ)
    ^ (2 - 1))) * (v 6))))) + (((2 * 1) * 1) * (v 8) + 1 * (((2 * 1) * (v 7) + 1 * ((2 * (v 6))))))) =
    (40 * v 0 + (34 * v 1 + (29 * v 2 + (40 * v 3 + (34 * v 4 + (29 * v 5 + (-12 * v 6 + (-10 * v 7 +
    (-8 * v 8 + (-10 * v 9 + 0))))))))))
  dsimp only [r₁, dr₁, r₂, dr₂, r₃, dr₃, e, de]
  simp only [nsmul_eq_mul]
  ring

#print axioms coefficient_strict_derivative_row_8
#assert_trust kernel coefficient_strict_derivative_row_8

end
end NLA.SP15

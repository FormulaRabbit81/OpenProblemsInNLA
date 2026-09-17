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

theorem coefficient_strict_derivative_row_7 :
    HasStrictFDerivAt (fun x : Parameters => coefficients x 7)
      ((ContinuousLinearMap.proj (7 : Fin 9) : Coefficients →L[ℝ] ℝ).comp
        coefficientDerivative) basePoint := by
  have h (i : Fin 10) := hasStrictFDerivAt_apply (𝕜 := ℝ) i basePoint
  have hr₁ := ((h 0).add (h 3))
  have hr₂ := ((h 1).add (h 4))
  have hr₃ := ((h 2).add (h 5))
  have he := (((h 8).pow 2).add ((h 9).pow 2))
  have hc := ((((((hr₁.mul hr₂).add (hr₁.mul hr₃)).add (hr₂.mul hr₃)).sub he).sub ((h 7).pow 2)).sub ((h
    6).pow 2))
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
  let de : ℝ := (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 8)) + ((2 • ((1 : ℝ) ^ (2 - 1))) * (v 9)))
  change ((((((r₁ * (dr₂) + r₂ * (dr₁)) + (r₁ * (dr₃) + r₃ * (dr₁))) + (r₂ * (dr₃) + r₃ * (dr₂))) - de)
    - ((2 • ((1 : ℝ) ^ (2 - 1))) * (v 7))) - ((2 • ((1 : ℝ) ^ (2 - 1))) * (v 6))) = (13 * v 0 + (12 * v
    1 + (11 * v 2 + (13 * v 3 + (12 * v 4 + (11 * v 5 + (-2 * v 6 + (-2 * v 7 + (-2 * v 8 + (-2 * v 9 +
    0))))))))))
  dsimp only [r₁, dr₁, r₂, dr₂, r₃, dr₃, de]
  simp only [nsmul_eq_mul]
  ring

#print axioms coefficient_strict_derivative_row_7
#assert_trust kernel coefficient_strict_derivative_row_7

end
end NLA.SP15

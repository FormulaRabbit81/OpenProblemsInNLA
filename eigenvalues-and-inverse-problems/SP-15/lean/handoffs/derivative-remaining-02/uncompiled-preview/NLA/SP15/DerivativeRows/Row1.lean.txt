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

theorem coefficient_strict_derivative_row_1 :
    HasStrictFDerivAt (fun x : Parameters => coefficients x 1)
      ((ContinuousLinearMap.proj (1 : Fin 9) : Coefficients →L[ℝ] ℝ).comp
        coefficientDerivative) basePoint := by
  have h (i : Fin 10) := hasStrictFDerivAt_apply (𝕜 := ℝ) i basePoint
  have ht₁ := ((h 0).mul (h 3))
  have ht₂ := ((h 1).mul (h 4))
  have ht₃ := ((h 2).mul (h 5))
  have he := (((h 8).pow 2).add ((h 9).pow 2))
  have hc := ((((((ht₁.mul ht₂).add (ht₁.mul ht₃)).add (ht₂.mul ht₃)).sub ((he.mul (h 1)).mul (h
    2))).sub ((((h 7).pow 2).mul (h 0)).mul (h 2))).sub ((((h 6).pow 2).mul (h 0)).mul (h 1)))
  refine hc.congr_fderiv ?_
  ext v
  rw [coefficient_derivative_row_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  let t₁ : ℝ := (1 * 4)
  let dt₁ : ℝ := (1 * (v 3) + 4 * (v 0))
  let t₂ : ℝ := (2 * 4)
  let dt₂ : ℝ := (2 * (v 4) + 4 * (v 1))
  let t₃ : ℝ := (3 * 4)
  let dt₃ : ℝ := (3 * (v 5) + 4 * (v 2))
  let e : ℝ := ((1 ^ 2) + (1 ^ 2))
  let de : ℝ := (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 8)) + ((2 • ((1 : ℝ) ^ (2 - 1))) * (v 9)))
  change ((((((t₁ * (dt₂) + t₂ * (dt₁)) + (t₁ * (dt₃) + t₃ * (dt₁))) + (t₂ * (dt₃) + t₃ * (dt₂))) - ((e
    * 2) * (v 2) + 3 * ((e * (v 1) + 2 * (de))))) - (((1 ^ 2) * 1) * (v 2) + 3 * (((1 ^ 2) * (v 0) + 1 *
    (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 7))))))) - (((1 ^ 2) * 1) * (v 1) + 2 * (((1 ^ 2) * (v 0) + 1 *
    (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 6))))))) = (75 * v 0 + (57 * v 1 + (43 * v 2 + (20 * v 3 + (32 * v
    4 + (36 * v 5 + (-4 * v 6 + (-6 * v 7 + (-12 * v 8 + (-12 * v 9 + 0))))))))))
  dsimp only [t₁, dt₁, t₂, dt₂, t₃, dt₃, e, de]
  simp only [nsmul_eq_mul]
  ring

#print axioms coefficient_strict_derivative_row_1
#assert_trust kernel coefficient_strict_derivative_row_1

end
end NLA.SP15

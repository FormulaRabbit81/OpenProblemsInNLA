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

theorem coefficient_strict_derivative_row_4 :
    HasStrictFDerivAt (fun x : Parameters => coefficients x 4)
      ((ContinuousLinearMap.proj (4 : Fin 9) : Coefficients →L[ℝ] ℝ).comp
        coefficientDerivative) basePoint := by
  have h (i : Fin 10) := hasStrictFDerivAt_apply (𝕜 := ℝ) i basePoint
  have hr₁ := ((h 0).add (h 3))
  have hr₂ := ((h 1).add (h 4))
  have hr₃ := ((h 2).add (h 5))
  have ht₁ := ((h 0).mul (h 3))
  have ht₂ := ((h 1).mul (h 4))
  have ht₃ := ((h 2).mul (h 5))
  have he := (((h 8).pow 2).add ((h 9).pow 2))
  have hc := (((((((((hr₁.mul ht₂).add (ht₁.mul hr₂)).add (hr₁.mul ht₃)).add (ht₁.mul hr₃)).add (hr₂.mul
    ht₃)).add (ht₂.mul hr₃)).sub (he.mul ((h 1).add (h 2)))).sub (((h 7).pow 2).mul ((h 0).add (h
    2)))).sub (((h 6).pow 2).mul ((h 0).add (h 1))))
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
  change (((((((((r₁ * (dt₂) + t₂ * (dr₁)) + (t₁ * (dr₂) + r₂ * (dt₁))) + (r₁ * (dt₃) + t₃ * (dr₁))) +
    (t₁ * (dr₃) + r₃ * (dt₁))) + (r₂ * (dt₃) + t₃ * (dr₂))) + (t₂ * (dr₃) + r₃ * (dt₂))) - (e * ((v 1 +
    v 2)) + (2 + 3) * (de))) - ((1 ^ 2) * ((v 0 + v 2)) + (1 + 3) * (((2 • ((1 : ℝ) ^ (2 - 1))) * (v
    7))))) - ((1 ^ 2) * ((v 0 + v 1)) + (1 + 2) * (((2 • ((1 : ℝ) ^ (2 - 1))) * (v 6))))) = (70 * v 0 +
    (61 * v 1 + (53 * v 2 + (33 * v 3 + (40 * v 4 + (45 * v 5 + (-6 * v 6 + (-8 * v 7 + (-10 * v 8 +
    (-10 * v 9 + 0))))))))))
  dsimp only [r₁, dr₁, r₂, dr₂, r₃, dr₃, t₁, dt₁, t₂, dt₂, t₃, dt₃, e, de]
  simp only [nsmul_eq_mul]
  ring

#print axioms coefficient_strict_derivative_row_4
#assert_trust kernel coefficient_strict_derivative_row_4

end
end NLA.SP15

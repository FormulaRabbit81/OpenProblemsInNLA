/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 attribution is retained in
Definitions.lean and SourceCorrespondence.md. Reuses Mathlib's exact complex
inner-product expansion; no numerical approximation or interval search is used.
-/
import NLA.IE02.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem descent_quadratic_expansion {n : ℕ} (T D : Square n) (ε : ℝ) (x : H n) :
    ‖euclideanLin (T - (ε : ℂ) • D) x‖ ^ 2 =
      ‖euclideanLin T x‖ ^ 2 - 2 * ε * descentForm T D x +
        ε ^ 2 * ‖euclideanLin D x‖ ^ 2 := by
  have haction : euclideanLin (T - (ε : ℂ) • D) x =
      euclideanLin T x - (ε : ℂ) • euclideanLin D x := by
    -- Expose the actual matrix-to-Euclidean-linear-map equivalence.
    change Matrix.toLpLin 2 2 (T - (ε : ℂ) • D) x =
      Matrix.toLpLin 2 2 T x - (ε : ℂ) • Matrix.toLpLin 2 2 D x
    rw [map_sub, map_smul]
    rfl
  rw [haction, norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, descentForm]
  ring

#print axioms descent_quadratic_expansion
#assert_trust kernel descent_quadratic_expansion

end
end NLA.IE02

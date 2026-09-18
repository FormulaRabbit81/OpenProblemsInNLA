/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original problem and approximation background
attribution to Tichý, Liesen, Faber and Courtney–Sarason is retained.

The exact complex Schur defect identity, including empty square matrices.
-/
import NLA.IE02.Definitions
import Mathlib.Tactic.Abel
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem schur_defect_identity {n : ℕ} (U : Square n) (c : ℂ) :
    (schurM U c).conjTranspose * schurM U c -
      (U - c • 1).conjTranspose * (U - c • 1) =
      (((1 - ‖c‖ ^ 2 : ℝ) : ℂ) • (1 - U.conjTranspose * U)) := by
  have hc : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * star c := by
    rw [Complex.sq_norm]
    exact (Complex.mul_conj c).symm
  -- Expand the two Gram products. The conjugate scalar cross terms cancel;
  -- only (1 - |c|²) times the original defect remains.
  simp only [schurM, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, star_star, sub_mul, mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one,
    Complex.ofReal_sub, Complex.ofReal_one, hc, sub_smul, smul_sub, one_smul,
    mul_comm (star c) c]
  abel

#print axioms schur_defect_identity
#assert_trust kernel schur_defect_identity

end
end NLA.IE02

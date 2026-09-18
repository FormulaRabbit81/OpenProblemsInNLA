/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.Definitions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem stein_identity {n : ℕ} (C R X₀ : Mat n)
    (hR : R.IsHermitian) (hX : X₀.det ≠ 0)
    (heq : X₀ + C.conjTranspose * X₀⁻¹ * C = R) :
    (hermitianImaginaryPart X₀).IsHermitian ∧
    hermitianImaginaryPart X₀ =
      (X₀⁻¹ * C).conjTranspose * hermitianImaginaryPart X₀ * (X₀⁻¹ * C) := by
  have hscalar : star ((2 * Complex.I : ℂ)⁻¹) = -(2 * Complex.I : ℂ)⁻¹ := by
    simp [Complex.star_def, mul_neg]
  constructor
  · -- IsHermitian is equality with conjugate transpose; expose it for the scalar-adjoint calculation.
    change (hermitianImaginaryPart X₀).conjTranspose = hermitianImaginaryPart X₀
    simp only [hermitianImaginaryPart, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, hscalar,
      neg_smul, ← smul_neg, neg_sub]
  · have hu : IsUnit X₀.det := isUnit_iff_ne_zero.mpr hX
    have hxi : X₀ * X₀⁻¹ = 1 := Matrix.mul_nonsing_inv X₀ hu
    have hstarxi : X₀⁻¹.conjTranspose * X₀.conjTranspose = 1 := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
        congrArg Matrix.conjTranspose hxi
    have hstarleft (A : Mat n) : X₀⁻¹.conjTranspose * (X₀.conjTranspose * A) = A := by
      rw [← Matrix.mul_assoc, hstarxi, Matrix.one_mul]
    have heqstar : X₀.conjTranspose + C.conjTranspose * X₀⁻¹.conjTranspose * C = R := by
      simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hR.eq, Matrix.mul_assoc] using
        congrArg Matrix.conjTranspose heq
    have hdiff : X₀ - X₀.conjTranspose =
        C.conjTranspose * X₀⁻¹.conjTranspose * C - C.conjTranspose * X₀⁻¹ * C := by
      calc
        X₀ - X₀.conjTranspose =
            (R - C.conjTranspose * X₀⁻¹ * C) -
              (R - C.conjTranspose * X₀⁻¹.conjTranspose * C) :=
          congrArg₂ (· - ·) (eq_sub_of_add_eq heq) (eq_sub_of_add_eq heqstar)
        _ = C.conjTranspose * X₀⁻¹.conjTranspose * C - C.conjTranspose * X₀⁻¹ * C := by
          abel
    have hcong : (X₀⁻¹ * C).conjTranspose * (X₀ - X₀.conjTranspose) * (X₀⁻¹ * C) =
        X₀ - X₀.conjTranspose := by
      calc
        (X₀⁻¹ * C).conjTranspose * (X₀ - X₀.conjTranspose) * (X₀⁻¹ * C) =
            C.conjTranspose * X₀⁻¹.conjTranspose * X₀ * X₀⁻¹ * C -
              C.conjTranspose * X₀⁻¹.conjTranspose * X₀.conjTranspose * X₀⁻¹ * C := by
          rw [Matrix.conjTranspose_mul]
          noncomm_ring
        _ = C.conjTranspose * X₀⁻¹.conjTranspose * C - C.conjTranspose * X₀⁻¹ * C := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left X₀ C hu, hstarleft]
        _ = X₀ - X₀.conjTranspose := hdiff.symm
    simpa only [hermitianImaginaryPart, Matrix.mul_smul, Matrix.smul_mul] using
      congrArg (fun A : Mat n => (2 * Complex.I : ℂ)⁻¹ • A) hcong.symm

#print axioms stein_identity

end NLA.MF18

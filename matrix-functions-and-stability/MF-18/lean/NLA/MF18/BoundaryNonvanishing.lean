/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. The homotopy and complex Green-function
argument are from George Stepaniants's solution of the Guo--Kuo--Lin question.
-/
import NLA.MF18.PencilAlgebra
import NLA.MF18.Positivity
import NLA.MF18.PairingAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

set_option autoImplicit false
open scoped BigOperators ComplexOrder

noncomputable section
namespace NLA.MF18

theorem homotopy_boundary_nonvanishing {n : ℕ} (C D R P : Mat n)
    (hR : R.IsHermitian) (hP : P.IsHermitian) (hpos : CirclePositive P D)
    (η : ℝ) (hη : 0 < η) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ∀ lam : ℂ, ‖lam‖ = 1 → (homotopyPolynomial C D R P η t).eval lam ≠ 0 := by
  intro lam hlam
  have hlam0 : lam ≠ 0 := by
    intro hz
    simpa [hz] using hlam
  have hstar : star lam = lam⁻¹ := (Complex.inv_eq_conj hlam).symm
  have hcross : (lam • C.conjTranspose + lam⁻¹ • C).IsHermitian := by
    simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, hstar]
      using Matrix.isHermitian_add_transpose_self (lam • C.conjTranspose)
  let H : Mat n := (t : ℂ) • (R - (lam • C.conjTranspose + lam⁻¹ • C))
  let K : Mat n := (1 - t) • P + t • (P - lam • D.conjTranspose - lam⁻¹ • D)
  have hH : H.IsHermitian := by
    exact (hR.sub hcross).smul (by simp [IsSelfAdjoint])
  obtain ⟨hp0, hsign⟩ := positive_average_and_sign P D hpos
  have hK : K.PosDef := by
    by_cases ht0 : t = 0
    · simpa [K, ht0] using hp0
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      exact Matrix.PosDef.posSemidef_add
        (hp0.posSemidef.smul (sub_nonneg.mpr ht.2)) ((hsign lam hlam).smul htp)
  have hdet := hermitian_add_imaginary_posDef_det_ne_zero H K hH hK η hη
  have heq : pencilValue ((t : ℂ) • regularizedA C D η)
      ((t : ℂ) • regularizedB C D η)
      ((t : ℂ) • R + (Complex.I * (η : ℂ)) • P) lam =
        (-lam) • (H + (Complex.I * (η : ℂ)) • K) := by
    ext i j
    simp only [pencilValue, regularizedA, regularizedB, H, K, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    field_simp [hlam0] <;> ring
  rw [homotopyPolynomial, pencil_evaluation, heq, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hlam0)) hdet

#print axioms homotopy_boundary_nonvanishing

end NLA.MF18

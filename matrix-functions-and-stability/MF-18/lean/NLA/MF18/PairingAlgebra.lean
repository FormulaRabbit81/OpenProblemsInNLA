/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.Definitions
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false
open scoped BigOperators ComplexOrder

noncomputable section
namespace NLA.MF18

theorem pairing_eq_dotProduct {n : ℕ} (H : Mat n) (v w : Vec n) :
    pairing H v w = star v ⬝ᵥ H.mulVec w := rfl

theorem pairing_add_matrix {n : ℕ} (H K : Mat n) (v w : Vec n) :
    pairing (H + K) v w = pairing H v w + pairing K v w := by
  simp only [pairing_eq_dotProduct, Matrix.add_mulVec, dotProduct_add]

theorem pairing_smul_matrix {n : ℕ} (c : ℂ) (H : Mat n) (v w : Vec n) :
    pairing (c • H) v w = c * pairing H v w := by
  simp only [pairing_eq_dotProduct, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem pairing_conjTranspose {n : ℕ} (H : Mat n) (v w : Vec n) :
    pairing H.conjTranspose v w = star (pairing H w v) := by
  simp only [pairing_eq_dotProduct, Matrix.mulVec_conjTranspose,
    Matrix.dotProduct_star, star_star, ← Matrix.dotProduct_mulVec]

theorem pairing_hermitian_im {n : ℕ} (H : Mat n) (hH : H.IsHermitian) (v : Vec n) :
    (pairing H v v).im = 0 := by
  have hs := pairing_conjTranspose H v v
  rw [hH.eq] at hs
  exact Complex.conj_eq_iff_im.mp hs.symm

theorem hermitian_add_imaginary_posDef_det_ne_zero {n : ℕ} (H K : Mat n)
    (hH : H.IsHermitian) (hK : K.PosDef) (η : ℝ) (hη : 0 < η) :
    (H + (Complex.I * (η : ℂ)) • K).det ≠ 0 := by
  have hu : IsUnit (H + (Complex.I * (η : ℂ)) • K) := by
    by_contra hnu
    obtain ⟨v, hv, hzero⟩ : ∃ v : Vec n, v ≠ 0 ∧
        (H + (Complex.I * (η : ℂ)) • K).mulVec v = 0 := by
      obtain ⟨a, b, hab⟩ := Function.not_injective_iff.mp <|
        Matrix.mulVec_injective_iff_isUnit.not.mpr hnu
      exact ⟨a - b, by simp [sub_eq_zero, hab, Matrix.mulVec_sub]⟩
    have hq : 0 < (pairing K v v).re :=
      (Complex.pos_iff.mp (hK.dotProduct_mulVec_pos hv)).1
    have hz : pairing H v v + (Complex.I * (η : ℂ)) * pairing K v v = 0 := by
      rw [← pairing_smul_matrix, ← pairing_add_matrix, pairing_eq_dotProduct,
        hzero, dotProduct_zero]
    have him : η * (pairing K v v).re = 0 := by
      simpa [Complex.mul_im, Complex.mul_re, pairing_hermitian_im H hH v] using
        congrArg Complex.im hz
    exact (mul_pos hη hq).ne' him
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

#print axioms hermitian_add_imaginary_posDef_det_ne_zero

end NLA.MF18

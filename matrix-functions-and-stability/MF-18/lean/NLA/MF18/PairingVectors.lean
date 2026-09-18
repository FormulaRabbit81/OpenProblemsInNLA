/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.PairingAlgebra

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem pairing_zero_left {n : ℕ} (H : Mat n) (w : Vec n) :
    pairing H 0 w = 0 := by
  simp only [pairing_eq_dotProduct, star_zero, zero_dotProduct]

theorem pairing_zero_right {n : ℕ} (H : Mat n) (v : Vec n) :
    pairing H v 0 = 0 := by
  simp only [pairing_eq_dotProduct, Matrix.mulVec_zero, dotProduct_zero]

theorem pairing_add_left {n : ℕ} (H : Mat n) (v₁ v₂ w : Vec n) :
    pairing H (v₁ + v₂) w = pairing H v₁ w + pairing H v₂ w := by
  simp only [pairing_eq_dotProduct, star_add, add_dotProduct]

theorem pairing_add_right {n : ℕ} (H : Mat n) (v w₁ w₂ : Vec n) :
    pairing H v (w₁ + w₂) = pairing H v w₁ + pairing H v w₂ := by
  simp only [pairing_eq_dotProduct, Matrix.mulVec_add, dotProduct_add]

theorem pairing_smul_left {n : ℕ} (H : Mat n) (a : ℂ) (v w : Vec n) :
    pairing H (a • v) w = star a * pairing H v w := by
  simp only [pairing_eq_dotProduct, star_smul, smul_dotProduct, smul_eq_mul]

theorem pairing_smul_right {n : ℕ} (H : Mat n) (a : ℂ) (v w : Vec n) :
    pairing H v (a • w) = a * pairing H v w := by
  simp only [pairing_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem pairing_conjugate_transform {n : ℕ} (S H : Mat n) (v w : Vec n) :
    pairing (S.conjTranspose * H * S) v w = pairing H (S.mulVec v) (S.mulVec w) := by
  simp only [pairing_eq_dotProduct, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]

#print axioms pairing_conjugate_transform

end NLA.MF18

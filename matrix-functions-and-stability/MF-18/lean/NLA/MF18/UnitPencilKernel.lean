/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.UnregularizedFactorization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem unit_pencil_left_pairing_zero {n : ℕ} (C R : Mat n) (hR : R.IsHermitian)
    (lam : ℂ) (hlam : ‖lam‖ = 1) (v : Vec n)
    (hv : (pencilValue C C.conjTranspose R lam).mulVec v = 0) :
    ∀ w : Vec n, pairing (pencilValue C C.conjTranspose R lam) v w = 0 := by
  have hlam0 : lam ≠ 0 := by
    intro hz
    simpa [hz] using hlam
  have hstar : star lam = lam⁻¹ := (Complex.inv_eq_conj hlam).symm
  let F : Mat n := lam • C.conjTranspose + lam⁻¹ • C - R
  have hF : F.IsHermitian := by
    apply Matrix.IsHermitian.sub _ hR
    simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, hstar]
      using Matrix.isHermitian_add_transpose_self (lam • C.conjTranspose)
  have hPF : pencilValue C C.conjTranspose R lam = lam • F := by
    ext i j
    simp only [pencilValue, F, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    field_simp [hlam0] <;> ring
  have hFv : F.mulVec v = 0 := by
    rw [hPF, Matrix.smul_mulVec] at hv
    exact (smul_eq_zero.mp hv).resolve_left hlam0
  intro w
  rw [hPF, pairing_smul_matrix]
  have hp : pairing F v w = 0 := by
    rw [← hF.eq, pairing_conjTranspose, pairing_eq_dotProduct, hFv,
      dotProduct_zero, star_zero]
  rw [hp, mul_zero]

#print axioms unit_pencil_left_pairing_zero

end NLA.MF18

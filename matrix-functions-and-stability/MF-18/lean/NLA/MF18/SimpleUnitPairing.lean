/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.UnitPencilKernel
import NLA.MF18.SimpleEigenfunctional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped ComplexOrder

noncomputable section
namespace NLA.MF18

/-- The exact simple-unit-root assertion, proved without an adjugate calculus bridge. -/
theorem simple_unit_root_pairing {n : ℕ} [NeZero n] (C R X₀ : Mat n)
    (hR : R.IsHermitian) (hX : X₀.det ≠ 0)
    (heq : X₀ + C.conjTranspose * X₀⁻¹ * C = R)
    (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hsimple : (unregularizedPolynomial C R).rootMultiplicity lam = 1)
    (v : Vec n) (hv : v ≠ 0) (heig : (X₀⁻¹ * C).mulVec v = lam • v) :
    pairing (hermitianImaginaryPart X₀) v v ≠ 0 := by
  obtain ⟨hsS, hdet⟩ := simple_root_factor_separation C R X₀ hX heq lam hsimple v hv heig
  let A : Mat n := lam • C.conjTranspose - X₀
  let f : Vec n →ₗ[ℂ] ℂ :=
    { toFun := fun w => pairing A v w
      map_add' := pairing_add_right A v
      map_smul' := by
        intro a w
        exact pairing_smul_right A a v w }
  have hfac : pencilValue C C.conjTranspose R lam =
      A * (lam • (1 : Mat n) - X₀⁻¹ * C) := by
    rw [unregularized_factorization C R X₀ hX heq lam,
      unregularized_left_factor C X₀ hX lam]
  have hinner : (lam • (1 : Mat n) - X₀⁻¹ * C).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig, sub_self]
  have hright : (pencilValue C C.conjTranspose R lam).mulVec v = 0 := by
    rw [hfac, ← Matrix.mulVec_mulVec, hinner, Matrix.mulVec_zero]
  have hpair := unit_pencil_left_pairing_zero C R hR lam hlam v hright
  have hf : ∀ w, f ((X₀⁻¹ * C).mulVec w) = lam * f w := by
    intro w
    have hh := hpair w
    rw [hfac, pairing_mul_matrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hh
    -- Fold the local linear functional f, whose value is pairing A v with its vector argument.
    change f (lam • w - (X₀⁻¹ * C).mulVec w) = 0 at hh
    rw [map_sub, map_smul, smul_eq_mul] at hh
    exact (sub_eq_zero.mp hh).symm
  have hfne : f ≠ 0 := by
    intro hfzero
    have hz : pairing A v (A⁻¹.mulVec v) = 0 := by
      -- The pairing is exactly f evaluated at A⁻¹v, allowing the assumed zero linear map to rewrite.
      change f (A⁻¹.mulVec v) = 0
      rw [hfzero, LinearMap.zero_apply]
    rw [pairing_eq_dotProduct, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] at hz
    exact hv (dotProduct_star_self_eq_zero.mp hz)
  have hfvv := simple_eigenfunctional_nonzero (X₀⁻¹ * C) lam hsS v hv heig f hfne hf
  have hCv : C.mulVec v = lam • X₀.mulVec v := by
    have hh := congrArg X₀.mulVec heig
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv_cancel_left X₀ C (isUnit_iff_ne_zero.mpr hX),
      Matrix.mulVec_smul] at hh
    exact hh
  have hpairC : pairing C v v = lam * pairing X₀ v v := by
    rw [pairing_eq_dotProduct, hCv, dotProduct_smul, smul_eq_mul]
    rfl
  have hlam0 : lam ≠ 0 := by
    intro hz
    simpa [hz] using hlam
  have hstar : star lam = lam⁻¹ := (Complex.inv_eq_conj hlam).symm
  have hfv : f v = star (pairing X₀ v v) - pairing X₀ v v := by
    -- Unfold the local functional f and its matrix A before expanding the sesquilinear pairing.
    change pairing (lam • C.conjTranspose - X₀) v v = _
    rw [pairing_sub_matrix, pairing_smul_matrix, pairing_conjTranspose,
      hpairC, star_mul, hstar]
    field_simp [hlam0] <;> ring
  intro hzero
  have hz : (2 * Complex.I : ℂ)⁻¹ *
      (pairing X₀ v v - star (pairing X₀ v v)) = 0 := by
    simpa only [hermitianImaginaryPart, pairing_smul_matrix, pairing_sub_matrix,
      pairing_conjTranspose] using hzero
  have hscalar : (2 * Complex.I : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hxeq : pairing X₀ v v = star (pairing X₀ v v) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hscalar)
  apply hfvv
  rw [hfv, ← hxeq, sub_self]

#print axioms simple_unit_root_pairing

end NLA.MF18

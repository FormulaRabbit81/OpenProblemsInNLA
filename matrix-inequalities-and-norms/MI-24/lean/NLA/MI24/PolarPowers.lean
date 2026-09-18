/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The polar unitary is constructed as W(W*W)^(-1/2). Mathlib's naturality of
the continuous functional calculus then proves the power-conjugation identity
used in Fujii's proof of Furuta's inequality. No polar or Furuta oracle is used.
-/
import NLA.MI24.GeometricCongruence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Algebra.Star.UnitaryStarAlgAut

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma star_mul_self_posDef {n : ℕ} (W : Mat n) (hW : IsUnit W) :
    (star W * W).PosDef := by
  simpa only [mul_one] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := (1 : Mat n)) hW).mpr
      Matrix.PosDef.one

lemma spectralPower_unitary_conjugate {n : ℕ} (U : unitary (Mat n))
    (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    spectralPower ((U : Mat n) * A * star (U : Mat n)) r =
      (U : Mat n) * spectralPower A r * star (U : Mat n) := by
  let φ := Unitary.conjStarAlgAut ℂ (Mat n) U
  have hc : ((U : Mat n) * A * star (U : Mat n)).PosDef :=
    (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (x := A) (Unitary.isUnit_coe (U := U))).mpr hA
  have hf : ContinuousOn (fun x : ℝ => x ^ r) (spectrum ℝ A) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    exact Or.inl (ne_of_gt (hA.isStrictlyPositive.spectrum_pos hx))
  have hφ : Continuous φ := by
    -- Forget only the bundled conjugation homomorphism φ and expose its
    -- underlying matrix multiplication map for continuity automation.
    change Continuous (fun X : Mat n => (U : Mat n) * X * star (U : Mat n))
    fun_prop
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ
    (fun x : ℝ => x ^ r) A hf hφ hA.isHermitian.isSelfAdjoint
    hc.isHermitian.isSelfAdjoint
  -- Expose spectralPower as CFC.rpow and the unitary-conjugation map;
  -- the following CFC rewrite then uses hmap with the same underlying map.
  change CFC.rpow ((U : Mat n) * A * star (U : Mat n)) r =
    (U : Mat n) * CFC.rpow A r * star (U : Mat n)
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hc.posSemidef.nonneg,
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  simpa only [φ, Unitary.conjStarAlgAut_apply, Unitary.coe_star] using hmap.symm

/-- An explicit polar factor, with reconstruction of the original matrix. -/
lemma exists_unitary_polar {n : ℕ} (W : Mat n) (hW : IsUnit W) :
    ∃ U : unitary (Mat n),
      W = (U : Mat n) * spectralPower (star W * W) (1 / 2) := by
  let M := star W * W
  let H := spectralPower M (1 / 2)
  let F := spectralPower M (-1 / 2)
  let V := W * F
  have hm : M.PosDef := star_mul_self_posDef W hW
  have hf : F.PosDef := spectralPower_posDef M hm _
  have hFH : F * H = 1 := neg_half_mul_half M hm
  have hHF : H * F = 1 := half_mul_neg_half M hm
  have hHH : H * H = M := spectralPower_half_mul_self M hm
  have hFMF : F * M * F = 1 := by
    rw [← hHH]
    calc
      F * (H * H) * F = (F * H) * (H * F) := by simp only [mul_assoc]
      _ = 1 := by rw [hFH, hHF]; simp
  have hVV : star V * V = 1 := by
    -- Expand the local polar factor V = W * F so star_mul and the
    -- inverse-square-root cancellation can act on its factors.
    change star (W * F) * (W * F) = 1
    rw [star_mul, hf.isHermitian.star_eq]
    calc
      (F * star W) * (W * F) = F * M * F := by dsimp only [M]; simp only [mul_assoc]
      _ = 1 := hFMF
  have hv : IsUnit V := hW.mul hf.isUnit
  refine ⟨⟨V, hv.mem_unitary_of_star_mul_self hVV⟩, ?_⟩
  -- Expose the constructed unitary subtype value V = W * F in the
  -- factorization goal; hFH then cancels the adjacent F/H factors.
  change W = (W * F) * H
  rw [mul_assoc, hFH, mul_one]

/-- Finite-dimensional form of Fujii's power-conjugation identity, valid for
every real exponent and every invertible complex matrix W. -/
lemma spectralPower_mul_star_conjugation {n : ℕ} (W : Mat n) (hW : IsUnit W)
    (r : ℝ) :
    spectralPower (W * star W) r =
      W * spectralPower (star W * W) (r - 1) * star W := by
  obtain ⟨U, hWpolar⟩ := exists_unitary_polar W hW
  let M := star W * W
  let H := spectralPower M (1 / 2)
  have hm : M.PosDef := star_mul_self_posDef W hW
  have hh : H.IsHermitian := spectralPower_isHermitian M hm _
  have hHH : H * H = M := spectralPower_half_mul_self M hm
  have hpolar : W = (U : Mat n) * H := hWpolar
  have hWW : W * star W = (U : Mat n) * M * star (U : Mat n) := by
    calc
      W * star W = ((U : Mat n) * H) * star ((U : Mat n) * H) := by rw [← hpolar]
      _ = (U : Mat n) * (H * H) * star (U : Mat n) := by
        rw [star_mul, hh.star_eq]
        simp only [mul_assoc]
      _ = (U : Mat n) * M * star (U : Mat n) := by rw [hHH]
  have hpowers : H * spectralPower M (r - 1) * H = spectralPower M r := by
    dsimp only [H]
    rw [spectralPower_mul M hm, spectralPower_mul M hm]
    congr 1
    ring
  calc
    spectralPower (W * star W) r =
        spectralPower ((U : Mat n) * M * star (U : Mat n)) r := by rw [hWW]
    _ = (U : Mat n) * spectralPower M r * star (U : Mat n) :=
      spectralPower_unitary_conjugate U M hm r
    _ = ((U : Mat n) * H) * spectralPower M (r - 1) *
        star ((U : Mat n) * H) := by
      rw [star_mul, hh.star_eq, ← hpowers]
      simp only [mul_assoc]
    _ = W * spectralPower M (r - 1) * star W := by rw [← hpolar]

end NLA.MI24

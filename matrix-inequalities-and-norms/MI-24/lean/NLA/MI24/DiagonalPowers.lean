/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Diagonal spectral powers are derived through the explicit diagonal star-algebra
homomorphism and coordinate evaluation. This avoids identifying Mathlib's chosen
eigenvector ordering with the original diagonal order. Finite spectra include zero.
-/
import NLA.MI24.SpectralPowers
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

def diagonalStarAlgHom (n : ℕ) : (Fin n → ℂ) →⋆ₐ[ℂ] Mat n :=
  { Matrix.diagonalAlgHom (n := Fin n) (α := ℂ) ℂ with
    map_star' := by
      intro v
      exact (Matrix.diagonal_conjTranspose v).symm }

lemma continuous_diagonalStarAlgHom (n : ℕ) : Continuous (diagonalStarAlgHom n) := by
  -- Forget only the bundled diagonalStarAlgHom to expose its toFun;
  -- reuse the pinned Continuous.matrix_diagonal theorem instead of proving
  -- coordinatewise continuity again.
  change Continuous (fun v : Fin n → ℂ => Matrix.diagonal v)
  exact (continuous_id : Continuous (fun v : Fin n → ℂ => v)).matrix_diagonal

lemma spectralPower_diagonal {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (r : ℝ) :
    spectralPower (Matrix.diagonal (fun i => (x i : ℂ))) r =
      Matrix.diagonal (fun i => ((x i ^ r : ℝ) : ℂ)) := by
  -- Supply the standard C-star-algebra construction directly on the finite Pi
  -- algebra; the matrix functional calculus remains the frozen matrix instance.
  letI : ContinuousFunctionalCalculus ℂ (Fin n → ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (Fin n → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let v : Fin n → ℂ := fun i => (x i : ℂ)
  have hv : 0 ≤ v := by
    intro i
    -- Expose the pointwise Pi order and local v coordinate as a real-to-
    -- complex cast; exact_mod_cast then transports the scalar nonnegativity.
    change (0 : ℂ) ≤ (x i : ℂ)
    exact_mod_cast hx i
  have hvself : IsSelfAdjoint v := Pi.isSelfAdjoint.mpr
    (fun i => IsSelfAdjoint.of_nonneg (hv i))
  have hA : (Matrix.diagonal v).PosSemidef := Matrix.PosSemidef.diagonal hv
  have hspec : spectrum ℝ v ⊆ Set.range x := by
    rw [Pi.spectrum_eq]
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    -- Expose this local v coordinate as algebraMap ℝ ℂ (x i), the precise
    -- form needed by the scalar-spectrum theorem CFC.spectrum_algebraMap_eq.
    change z ∈ spectrum ℝ (algebraMap ℝ ℂ (x i)) at hi
    rw [CFC.spectrum_algebraMap_eq] at hi
    exact ⟨i, (Set.mem_singleton_iff.mp hi).symm⟩
  have hf : ContinuousOn (fun z : ℝ => z ^ r) (spectrum ℝ v) :=
    ((Set.finite_range x).subset hspec).continuousOn _
  have hPi : cfc (fun z : ℝ => z ^ r) v = fun i => ((x i ^ r : ℝ) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) _ v (by rwa [← Pi.spectrum_eq]) hvself
      (fun i => IsSelfAdjoint.of_nonneg (hv i))]
    funext i
    exact cfc_algebraMap (R := ℝ) (A := ℂ) (x i) (fun z : ℝ => z ^ r)
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (diagonalStarAlgHom n)
    (fun z : ℝ => z ^ r) v hf (continuous_diagonalStarAlgHom n)
    hvself hA.isHermitian.isSelfAdjoint
  calc
    _ = cfc (fun z : ℝ => z ^ r) (Matrix.diagonal v) := by
      simpa only [spectralPower, CFC.rpow_eq_pow] using
        CFC.rpow_eq_cfc_real (a := Matrix.diagonal v) (y := r) hA.nonneg
    _ = diagonalStarAlgHom n (cfc (fun z : ℝ => z ^ r) v) := hmap.symm
    _ = _ := by rw [hPi]; rfl

end NLA.MI24

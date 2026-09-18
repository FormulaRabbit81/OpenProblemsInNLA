/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Mathlib's symbolic determinant bound supplies all minor bounds at once. The
dimension factor is independent of word length; no permutation is enumerated.
The reused Euclidean operator-entry estimate retains its MF07 authorship.
-/
import NLA.MF06.CompoundAlgebra
import NLA.MF07.BlockComparison
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

theorem compound_norm_bound {d : ℕ} (k : ℕ) (hk : k ≤ d) (A : Square d) :
    0 < compoundNormConstant d k ∧
    spectralNorm (compoundMatrix k A) ≤ compoundNormConstant d k * spectralNorm A ^ k := by
  have hdim : 0 < (compoundDim d k : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le ((compound_dimensions d k).2 hk))
  have hfactorial : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hentry (i j : Fin (compoundDim d k)) :
      ‖compoundMatrix k A i j‖ ≤ (Nat.factorial k : ℝ) * spectralNorm A ^ k := by
    have h := Matrix.det_le
      (A := A.submatrix (minorCoordinate d k i) (minorCoordinate d k j))
      (abv := NormedField.toAbsoluteValue ℂ)
      (x := spectralNorm A)
      (fun u v => spectralNorm_entry_bound A (minorCoordinate d k i u)
        (minorCoordinate d k j v))
    -- The absolute-value structure is the complex norm, and the determinant
    -- is the frozen sorted minor defining this compound-matrix entry.
    change ‖compoundMatrix k A i j‖ ≤
      Nat.factorial (Fintype.card (Fin k)) • spectralNorm A ^ Fintype.card (Fin k) at h
    simpa only [Fintype.card_fin, nsmul_eq_mul] using h
  refine ⟨mul_pos hdim hfactorial, ?_⟩
  calc
    spectralNorm (compoundMatrix k A) ≤
        (compoundDim d k : ℝ) * ((Nat.factorial k : ℝ) * spectralNorm A ^ k) :=
      spectralNorm_le_card_mul_entry_bound _ _
        (mul_nonneg hfactorial.le (pow_nonneg (spectralNorm_nonneg A) k)) hentry
    _ = compoundNormConstant d k * spectralNorm A ^ k := by
      unfold compoundNormConstant
      ring

#print axioms compound_norm_bound
#assert_trust kernel compound_norm_bound

end NLA.MF06

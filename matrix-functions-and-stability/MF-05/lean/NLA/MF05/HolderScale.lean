/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical optimization:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, proof of Theorem 2.

The scale is the actual positive real d-th root of L / delta. Its exact d-th
power converts the perturbation term to d * L / scale. Real-power division
then gives the displayed Holder coefficient, including when d = 1.
-/
import NLA.MF05.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05

theorem holder_scale_identity {d : ℕ} (hd : 1 ≤ d) (L delta : ℝ)
    (hL : 0 < L) (hdelta : 0 < delta) (hdeltaL : delta ≤ L) :
    1 ≤ holderScale d L delta ∧
    (holderScale d L delta) ^ d = L / delta ∧
    L / holderScale d L delta =
      Real.rpow L (1 - 1 / (d : ℝ)) * Real.rpow delta (1 / (d : ℝ)) ∧
    2 * (d : ℝ) ^ 2 * L / holderScale d L delta +
        comparisonFactor d (holderScale d L delta) * delta =
      holderConstant d L * Real.rpow delta (1 / (d : ℝ)) := by
  have hscale : 1 ≤ holderScale d L delta := by
    simpa only [holderScale, Real.rpow_eq_pow] using
      Real.one_le_rpow ((one_le_div hdelta).mpr hdeltaL)
        (div_nonneg zero_le_one (Nat.cast_nonneg d))
  have hscale_pos : 0 < holderScale d L delta := lt_of_lt_of_le zero_lt_one hscale
  have hpower : (holderScale d L delta) ^ d = L / delta := by
    simpa only [holderScale, Real.rpow_eq_pow, one_div] using
      Real.rpow_inv_natCast_pow (n := d) (div_nonneg hL.le hdelta.le) (by omega)
  have hratio : L / holderScale d L delta =
      Real.rpow L (1 - 1 / (d : ℝ)) * Real.rpow delta (1 / (d : ℝ)) := by
    dsimp only [holderScale]
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow hL.le hdelta.le, Real.rpow_sub hL, Real.rpow_one]
    simp only [div_div_eq_mul_div, div_mul_eq_mul_div]
  have hreduce : (holderScale d L delta) ^ (d - 1) * delta =
      L / holderScale d L delta := by
    apply (eq_div_iff hscale_pos.ne').mpr
    calc
      ((holderScale d L delta) ^ (d - 1) * delta) * holderScale d L delta =
          (holderScale d L delta) ^ (d - 1 + 1) * delta := by
        rw [pow_succ]
        ring
      _ = (holderScale d L delta) ^ d * delta := by rw [Nat.sub_add_cancel hd]
      _ = L := by rw [hpower, div_mul_cancel₀ _ hdelta.ne']
  have hfactor : comparisonFactor d (holderScale d L delta) * delta =
      (d : ℝ) * (L / holderScale d L delta) := by
    dsimp only [comparisonFactor]
    rw [mul_assoc, hreduce]
  refine ⟨hscale, hpower, hratio, ?_⟩
  calc
    2 * (d : ℝ) ^ 2 * L / holderScale d L delta +
        comparisonFactor d (holderScale d L delta) * delta =
        (2 * (d : ℝ) ^ 2 + (d : ℝ)) * (L / holderScale d L delta) := by
      rw [hfactor, mul_div_assoc]
      ring
    _ = holderConstant d L * Real.rpow delta (1 / (d : ℝ)) := by
      rw [hratio]
      dsimp only [holderConstant]
      ring

#print axioms holder_scale_identity
#assert_trust kernel holder_scale_identity

end NLA.MF05

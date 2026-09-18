/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Theorem 2.

Both families vary independently in one common spectral-norm ball. The
optimized transfer estimate handles positive distance at most L. Compact-set
equality handles distance zero; the actual radius bounds in [0,L] handle
larger distances. No positivity of either radius is required.
-/
import NLA.MF05.RadiusTransfer
import NLA.MF05.HolderScale

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

lemma holderConstant_pos {d : ℕ} (hd : 1 ≤ d) (L : ℝ) (hL : 0 < L) :
    0 < holderConstant d L := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
  have hdpos : (0 : ℝ) < (d : ℝ) := zero_lt_one.trans_le hd1
  have hlinear : 0 < 2 * (d : ℝ) + 1 := by linarith only [hd1]
  exact mul_pos (mul_pos hdpos hlinear)
    (Real.rpow_pos_of_pos hL (1 - 1 / (d : ℝ)))

/-- Compact norm attainment transfers a generator bound to the actual radius.
The full root-limit semantics supplies both radius inequalities. -/
lemma jointSpectralRadius_bounds_of_inNormBall {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L : ℝ) (hML : InNormBall M L) :
    0 ≤ jointSpectralRadius M ∧ jointSpectralRadius M ≤ L := by
  obtain ⟨hr0, hrnorm, _⟩ := general_root_limit_semantics hd M hM hne
  refine ⟨hr0, hrnorm.trans ?_⟩
  obtain ⟨_, ⟨A, hA, hvalue⟩, _⟩ := family_norm_maximum hd M hM hne
  rw [← hvalue]
  exact hML A hA

/-- At distance at least L, the proposed Holder bound already dominates L.
The complementary powers of the positive base L multiply exactly to L. -/
lemma holder_bound_ge_norm_bound {d : ℕ} (hd : 1 ≤ d) (L delta : ℝ)
    (hL : 0 < L) (hLdelta : L ≤ delta) :
    L ≤ holderConstant d L * Real.rpow delta (1 / (d : ℝ)) := by
  have hC := holderConstant_pos hd L hL
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
  have hcoefficient : 1 ≤ (d : ℝ) * (2 * (d : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hd1 (by linarith only [hd1])
  have hpowers : Real.rpow L (1 - 1 / (d : ℝ)) * Real.rpow L (1 / (d : ℝ)) = L := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hL, sub_add_cancel, Real.rpow_one]
  have hsame : holderConstant d L * Real.rpow L (1 / (d : ℝ)) =
      (d : ℝ) * (2 * (d : ℝ) + 1) * L := by
    dsimp only [holderConstant]
    rw [mul_assoc, hpowers]
  have hmono : Real.rpow L (1 / (d : ℝ)) ≤ Real.rpow delta (1 / (d : ℝ)) :=
    Real.rpow_le_rpow hL.le hLdelta (div_nonneg zero_le_one (Nat.cast_nonneg d))
  calc
    L ≤ (d : ℝ) * (2 * (d : ℝ) + 1) * L := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoefficient hL.le
    _ = holderConstant d L * Real.rpow L (1 / (d : ℝ)) := hsame.symm
    _ ≤ holderConstant d L * Real.rpow delta (1 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono hC.le

theorem uniform_holder_estimate {d : ℕ} (hd : 1 ≤ d) (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hNL : InNormBall N L) :
    0 < holderConstant d L ∧
    |jointSpectralRadius M - jointSpectralRadius N| ≤
      holderConstant d L * Real.rpow (spectralHausdorff M N) (1 / (d : ℝ)) := by
  have hC := holderConstant_pos hd L hL
  refine ⟨hC, ?_⟩
  obtain ⟨_, _, _, _, hdelta0, hsym, hzero, _, _⟩ :=
    spectral_hausdorff_semantics M N hM hneM hN hneN
  by_cases hz : spectralHausdorff M N = 0
  · have hMN : M = N := hzero.mp hz
    have hdiff : jointSpectralRadius M - jointSpectralRadius N = 0 := by
      rw [hMN, sub_self]
    rw [hdiff, abs_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg hdelta0 _)
  · have hdelta : 0 < spectralHausdorff M N := lt_of_le_of_ne hdelta0 (Ne.symm hz)
    by_cases hdeltaL : spectralHausdorff M N ≤ L
    · obtain ⟨hs, _, _, hopt⟩ := holder_scale_identity hd L (spectralHausdorff M N)
        hL hdelta hdeltaL
      have hMN := hausdorff_radius_transfer hd M N hM hneM hN hneN L
        (holderScale d L (spectralHausdorff M N)) hL hML hs
      have hNM := hausdorff_radius_transfer hd N M hN hneN hM hneM L
        (holderScale d L (spectralHausdorff M N)) hL hNL hs
      rw [← hsym] at hNM
      dsimp only [comparisonRate] at hMN hNM
      apply abs_le'.mpr
      constructor
      · linarith only [hNM, hopt]
      · linarith only [hMN, hopt]
    · obtain ⟨hrM0, hrML⟩ := jointSpectralRadius_bounds_of_inNormBall hd M hM hneM L hML
      obtain ⟨hrN0, hrNL⟩ := jointSpectralRadius_bounds_of_inNormBall hd N hN hneN L hNL
      have hdiffL : |jointSpectralRadius M - jointSpectralRadius N| ≤ L := by
        apply abs_le'.mpr
        constructor <;> linarith only [hrM0, hrML, hrN0, hrNL]
      exact hdiffL.trans (holder_bound_ge_norm_bound hd L (spectralHausdorff M N)
        hL (lt_of_not_ge hdeltaL).le)

#print axioms uniform_holder_estimate
#assert_trust kernel uniform_holder_estimate

end NLA.MF05

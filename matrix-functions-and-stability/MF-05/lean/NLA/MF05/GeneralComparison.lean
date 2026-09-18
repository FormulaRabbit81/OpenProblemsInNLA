/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Proposition 5.

The exact published MF07 comparison is used on the complete normalized compact
family. At radius zero, scalar-identity adjunction supplies positive radii,
and only a fixed-length scalar polynomial is passed to the limit. Continuity
of the joint spectral radius is not a hypothesis of this argument.
-/
import NLA.MF05.Scaling
import NLA.MF05.IdentityAdjoin
import NLA.MF07.QuantitativeComparison

set_option autoImplicit false
set_option leancert.trust "kernel"
open Filter Topology

noncomputable section
namespace NLA.MF05
open NLA.MF07

/-- Normalize the whole family by its positive radius, consume the unchanged
radius-one comparison, and cancel the scalar at the same word length. -/
lemma positive_radius_quantitative_comparison {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (hr : 0 < jointSpectralRadius M) (L s : ℝ) (hML : familyNorm M ≤ L)
    (hs : 1 ≤ s) (n : ℕ) :
    familyGrowth M n ≤ comparisonFactor d s * (comparisonRate d M L s) ^ n := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  obtain ⟨hscaled, hnescaled, hnormscaled, hgrowthscaled, hradscaled⟩ :=
    positive_scaling_semantics hd M hM hne (jointSpectralRadius M)⁻¹ (inv_pos.mpr hr)
  have hnormalized : jointSpectralRadius (scaledFamily (jointSpectralRadius M)⁻¹ M) = 1 :=
    hradscaled.trans (inv_mul_cancel₀ hr.ne')
  have hcomparison := NLA.MF07.quantitative_comparison hd _ hscaled hnescaled
    hnormalized s hs n
  have hrate : jointSpectralRadius M *
      (1 + 2 * (d : ℝ) ^ 2 * ((jointSpectralRadius M)⁻¹ * familyNorm M) / s) =
      jointSpectralRadius M + 2 * (d : ℝ) ^ 2 * familyNorm M / s := by
    field_simp [hr.ne', hspos.ne']
  have hnative : familyGrowth M n ≤ comparisonFactor d s *
      (jointSpectralRadius M + 2 * (d : ℝ) ^ 2 * familyNorm M / s) ^ n := by
    calc
      familyGrowth M n = (jointSpectralRadius M) ^ n *
          familyGrowth (scaledFamily (jointSpectralRadius M)⁻¹ M) n := by
        rw [hgrowthscaled n, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne',
          one_pow, one_mul]
      _ ≤ (jointSpectralRadius M) ^ n * (comparisonFactor d s *
          (1 + 2 * (d : ℝ) ^ 2 *
            familyNorm (scaledFamily (jointSpectralRadius M)⁻¹ M) / s) ^ n) :=
        mul_le_mul_of_nonneg_left hcomparison (pow_nonneg hr.le n)
      _ = comparisonFactor d s *
          (jointSpectralRadius M + 2 * (d : ℝ) ^ 2 * familyNorm M / s) ^ n := by
        rw [hnormscaled, mul_left_comm, ← mul_pow, hrate]
  have hdim : 0 ≤ 2 * (d : ℝ) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have hnorm0 : 0 ≤ familyNorm M := (family_norm_maximum hd M hM hne).1
  have hrate0 : 0 ≤ jointSpectralRadius M + 2 * (d : ℝ) ^ 2 * familyNorm M / s :=
    add_nonneg hr.le (div_nonneg (mul_nonneg hdim hnorm0) hspos.le)
  have hrate_le : jointSpectralRadius M + 2 * (d : ℝ) ^ 2 * familyNorm M / s ≤
      comparisonRate d M L s :=
    add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hML hdim) hspos.le)
  have hfactor : 0 ≤ comparisonFactor d s :=
    mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hspos.le _)
  exact hnative.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hrate0 hrate_le n) hfactor)

theorem general_quantitative_comparison {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L s : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hs : 1 ≤ s) (n : ℕ) :
    familyGrowth M n ≤ comparisonFactor d s * (comparisonRate d M L s) ^ n := by
  have hnorm : familyNorm M ≤ L := by
    obtain ⟨_, ⟨A, hA, hvalue⟩, _⟩ := family_norm_maximum hd M hM hne
    rw [← hvalue]
    exact hML A hA
  by_cases hr : 0 < jointSpectralRadius M
  · exact positive_radius_quantitative_comparison hd M hM hne hr L s hnorm hs n
  · have hr0 : jointSpectralRadius M = 0 :=
      le_antisymm (le_of_not_gt hr) (jointSpectralRadius_nonneg M hM hne)
    have hbound : ∀ e : ℝ, 0 < e → e < L →
        familyGrowth M n ≤ comparisonFactor d s *
          (e + 2 * (d : ℝ) ^ 2 * L / s) ^ n := by
      intro e he heL
      obtain ⟨hN, hneN, hNnorm, hNrad⟩ := scalar_identity_adjoin_radius hd M hM hne e he
      have hrN : jointSpectralRadius (identityAdjoin e M) = e := by
        rw [hNrad, hr0, max_eq_right he.le]
      have hnormN : familyNorm (identityAdjoin e M) ≤ L := by
        rw [hNnorm]
        exact max_le hnorm heL.le
      have hpositive := positive_radius_quantitative_comparison hd _ hN hneN
        (by rwa [hrN]) L s hnormN hs n
      have hsubset := familyGrowth_le_of_subset M (identityAdjoin e M) hM hne hN
        (Set.subset_insert _ _) n
      exact hsubset.trans (by simpa only [comparisonRate, hrN] using hpositive)
    have hcontinuous : Continuous (fun e : ℝ => comparisonFactor d s *
        (e + 2 * (d : ℝ) ^ 2 * L / s) ^ n) := by
      fun_prop
    have hlimit := hcontinuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
    have heL : ∀ᶠ e : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0, e < L :=
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hL)
    dsimp only [comparisonRate]
    rw [hr0]
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin, heL] with e he heL
    exact hbound e he heL

#print axioms general_quantitative_comparison
#assert_trust kernel general_quantitative_comparison

end NLA.MF05

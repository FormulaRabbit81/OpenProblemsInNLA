/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The zero-radius case follows from nonnegativity without inversion. For every
positive radius, actual scalar image identities normalize the reference and
rescale both the radius and the Hausdorff neighborhood exactly.
-/
import NLA.MF06.NormalizedLower
import NLA.MF06.HausdorffScaling

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

theorem canonical_pointwise_lower_lipschitz {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        jointSpectralRadius M - C * canonicalHausdorff M N ≤ jointSpectralRadius N := by
  have hnonneg := jointSpectralRadius_nonneg M hM hneM
  rcases eq_or_lt_of_le hnonneg with hzero | hpositive
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
    intro N hN hneN _
    have hδ := canonicalHausdorff_nonneg M N hM hneM hN hneN
    have hN0 := jointSpectralRadius_nonneg N hN hneN
    rw [← hzero, one_mul]
    linarith
  · let c : ℝ := (jointSpectralRadius M)⁻¹
    have hc : 0 < c := inv_pos.mpr hpositive
    have hcρ : c * jointSpectralRadius M = 1 := inv_mul_cancel₀ (ne_of_gt hpositive)
    have hsM := positive_scaling_semantics hd M hM hneM c hc
    have hsρ : jointSpectralRadius (scaledFamily c M) = 1 := hsM.2.2.2.2.trans hcρ
    obtain ⟨r₀, hr₀, C, hC, hlower⟩ := normalized_pointwise_lower_lipschitz hd
      (scaledFamily c M) hsM.1 hsM.2.1 hsρ
    refine ⟨r₀ / c, div_pos hr₀ hc, C, hC, ?_⟩
    intro N hN hneN hnear
    have hsN := positive_scaling_semantics hd N hN hneN c hc
    have hscaledDist := positive_hausdorff_scaling M N hM hneM hN hneN c hc
    have hscaledNear : canonicalHausdorff (scaledFamily c M) (scaledFamily c N) < r₀ := by
      rw [hscaledDist]
      simpa only [mul_comm] using (lt_div_iff₀ hc).mp hnear
    have hscaled := hlower (scaledFamily c N) hsN.1 hsN.2.1 hscaledNear
    rw [hscaledDist, hsN.2.2.2.2] at hscaled
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      c * (jointSpectralRadius M - C * canonicalHausdorff M N) =
          1 - C * (c * canonicalHausdorff M N) := by
        calc
          _ = c * jointSpectralRadius M - C * (c * canonicalHausdorff M N) := by ring
          _ = _ := by rw [hcρ]
      _ ≤ c * jointSpectralRadius N := hscaled

#print axioms canonical_pointwise_lower_lipschitz
#assert_trust kernel canonical_pointwise_lower_lipschitz

end NLA.MF06

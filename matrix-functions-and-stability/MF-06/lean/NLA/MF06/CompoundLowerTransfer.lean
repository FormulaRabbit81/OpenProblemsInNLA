/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
Reused MF05/MF07 mathematics retain the attribution in their pinned sources.

Transfer a proved product-bounded critical exterior degree to the original
family. All neighborhood constants are chosen before the perturbing family.
This helper's exterior hypotheses are discharged by C33 in the final theorem.
-/
import NLA.MF06.ProductBoundedLower
import NLA.MF06.CompoundFirstDegree
import NLA.MF06.CompoundHausdorff
import NLA.MF06.RootLowerBound
import NLA.MF05.LocalBall

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma lower_lipschitz_of_critical_compound {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (k : ℕ) (hk0 : 1 ≤ k) (hkd : k ≤ d)
    (hcritical : jointSpectralRadius (compoundFamily k M) = 1)
    (hbounded : IsProductBounded (compoundFamily k M)) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        1 - C * canonicalHausdorff M N ≤ jointSpectralRadius N := by
  have hdim := (compound_dimensions d k).2 hkd
  obtain ⟨hCM, hneCM, _⟩ := (compound_family_semantics hd M hM hneM).1 k hkd
  obtain ⟨r₀, hr₀, C₀, hC₀, hlower⟩ :=
    product_bounded_lower_lipschitz hdim (compoundFamily k M) hCM hneCM hbounded hcritical
  obtain ⟨hL, hball⟩ := local_common_norm_ball hd M hM hneM
  have hML : InNormBall M (localNormBound M) := by
    apply hball M hM hneM
    simpa only [spectralHausdorff, Metric.hausdorffDist_self_zero] using half_radius_certificate.1
  let D : ℝ := compoundLipschitzConstant d k (localNormBound M)
  obtain ⟨A, hA⟩ := hneM
  have hD : 0 < D :=
    (compound_local_lipschitz k hk0 hkd _ hL A A (hML A hA) (hML A hA)).1
  let r : ℝ := min localRadius (min (r₀ / D) (1 / (C₀ * D)))
  let C : ℝ := C₀ * D
  have hC : 0 < C := mul_pos hC₀ hD
  have hr : 0 < r := lt_min half_radius_certificate.1
    (lt_min (div_pos hr₀ hD) (div_pos zero_lt_one hC))
  refine ⟨r, hr, C, hC, ?_⟩
  intro N hN hneN hnear
  have hswap : spectralHausdorff N M = canonicalHausdorff M N := by
    calc
      spectralHausdorff N M = spectralHausdorff M N := Metric.hausdorffDist_comm
      _ = canonicalHausdorff M N := spectralHausdorff_eq_canonical M N hM ⟨A, hA⟩ hN hneN
  have hnearball : canonicalHausdorff M N < localRadius :=
    lt_of_lt_of_le hnear (min_le_left _ _)
  have hNL : InNormBall N (localNormBound M) := hball N hN hneN (hswap.symm ▸ hnearball)
  have hdist := compound_hausdorff_bound k hk0 hkd M N hM ⟨A, hA⟩ hN hneN
    (localNormBound M) hL hML hNL
  have hnearD : canonicalHausdorff M N < r₀ / D :=
    lt_of_lt_of_le hnear ((min_le_right _ _).trans (min_le_left _ _))
  have hnearC : canonicalHausdorff M N < 1 / C :=
    lt_of_lt_of_le hnear ((min_le_right _ _).trans (min_le_right _ _))
  have hCD : D * canonicalHausdorff M N < r₀ := by
    simpa only [mul_comm] using (lt_div_iff₀ hD).mp hnearD
  have hCδ : C * canonicalHausdorff M N < 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hC).mp hnearC
  obtain ⟨hCN, hneCN, hpower⟩ := (compound_family_semantics hd N hN hneN).1 k hkd
  have hcomp := hlower (compoundFamily k N) hCN hneCN (hdist.trans_lt hCD)
  have hδ := canonicalHausdorff_nonneg M N hM ⟨A, hA⟩ hN hneN
  apply root_lower_bound k hk0 (jointSpectralRadius N) (1 - C * canonicalHausdorff M N)
    (jointSpectralRadius_nonneg N hN hneN) (by linarith) (by nlinarith [mul_nonneg hC.le hδ])
  calc
    1 - C * canonicalHausdorff M N = 1 - C₀ * (D * canonicalHausdorff M N) := by
      dsimp only [C]; ring
    _ ≤ 1 - C₀ * canonicalHausdorff (compoundFamily k M) (compoundFamily k N) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hdist hC₀.le) 1
    _ ≤ jointSpectralRadius (compoundFamily k N) := hcomp
    _ ≤ jointSpectralRadius N ^ k := hpower

#print axioms lower_lipschitz_of_critical_compound
#assert_trust kernel lower_lipschitz_of_critical_compound

end NLA.MF06

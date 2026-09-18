/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
Reused MF05 radius/scaling definitions retain Matthew J. Colbrook's credit.

Positive homothety first bounds both nearest-generator directions. Its
literal reciprocal image gives the reverse bound; only the stated positive
scalar is inverted. No positive-radius assumption is hidden in this lemma.
-/
import NLA.MF06.HausdorffImages
import NLA.MF05.Scaling

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma scaledFamily_reciprocal {d : ℕ} (M : Set (Square d)) (c : ℝ) (hc : 0 < c) :
    scaledFamily c⁻¹ (scaledFamily c M) = M := by
  have hscalar : (↑c⁻¹ : ℂ) * (c : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hc), Complex.ofReal_one]
  unfold scaledFamily
  rw [Set.image_image]
  have hmap : (fun A : Square d => (↑c⁻¹ : ℂ) • ((c : ℂ) • A)) = id := by
    funext A
    simp only [smul_smul, hscalar, one_smul, id_eq]
  rw [hmap, Set.image_id]

lemma positive_hausdorff_scaling_le {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (c : ℝ) (hc : 0 < c) :
    canonicalHausdorff (scaledFamily c M) (scaledFamily c N) ≤ c * canonicalHausdorff M N := by
  apply canonicalHausdorff_image_le M N hM hneM hN hneN
    (fun A : Square d => (c : ℂ) • A) (continuous_const_smul _) c hc.le
  intro A _ B _
  rw [← smul_sub, spectralNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, le_refl]

theorem positive_hausdorff_scaling {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (c : ℝ) (hc : 0 < c) :
    canonicalHausdorff (scaledFamily c M) (scaledFamily c N) = c * canonicalHausdorff M N := by
  apply le_antisymm (positive_hausdorff_scaling_le M N hM hneM hN hneN c hc)
  have hi := positive_hausdorff_scaling_le (scaledFamily c M) (scaledFamily c N)
    (scaledFamily_isCompact M hM c) (scaledFamily_nonempty M hneM c)
    (scaledFamily_isCompact N hN c) (scaledFamily_nonempty N hneN c) c⁻¹ (inv_pos.mpr hc)
  rw [scaledFamily_reciprocal M c hc, scaledFamily_reciprocal N c hc] at hi
  have hmul := mul_le_mul_of_nonneg_left hi hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] using hmul

#print axioms positive_hausdorff_scaling
#assert_trust kernel positive_hausdorff_scaling

end NLA.MF06

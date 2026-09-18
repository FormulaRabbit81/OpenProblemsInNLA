/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The reused canonical Hausdorff identification retains MF05/Colbrook credit.

Compact nearest-generator matching in both directions transfers actual
spectral distance estimates to the literal canonical sup-inf distance.
-/
import NLA.MF06.Definitions
import NLA.MF05.Hausdorff

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma canonicalHausdorff_nonneg {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty) :
    0 ≤ canonicalHausdorff M N := by
  rw [← spectralHausdorff_eq_canonical M N hM hneM hN hneN]
  exact Metric.hausdorffDist_nonneg

lemma canonicalHausdorff_le_of_matches {d : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (D : ℝ) (hD : 0 ≤ D)
    (hMN : ∀ A ∈ M, ∃ B ∈ N, spectralNorm (A - B) ≤ D)
    (hNM : ∀ B ∈ N, ∃ A ∈ M, spectralNorm (B - A) ≤ D) :
    canonicalHausdorff M N ≤ D := by
  rw [← spectralHausdorff_eq_canonical M N hM hneM hN hneN]
  apply Metric.hausdorffDist_le_of_mem_dist hD
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨B, hB, hdist⟩ := hMN A hA
    exact ⟨Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) B, ⟨B, hB, rfl⟩,
      (spectral_operator_distance A B).trans_le hdist⟩
  · rintro _ ⟨B, hB, rfl⟩
    obtain ⟨A, hA, hdist⟩ := hNM B hB
    exact ⟨Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A, ⟨A, hA, rfl⟩,
      (spectral_operator_distance B A).trans_le hdist⟩

lemma canonicalHausdorff_image_le {d m : ℕ} (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (f : Square d → Square m) (hf : Continuous f) (K : ℝ) (hK : 0 ≤ K)
    (hL : ∀ A ∈ M ∪ N, ∀ B ∈ M ∪ N,
      spectralNorm (f A - f B) ≤ K * spectralNorm (A - B)) :
    canonicalHausdorff (f '' M) (f '' N) ≤ K * canonicalHausdorff M N := by
  have heq := spectralHausdorff_eq_canonical M N hM hneM hN hneN
  apply canonicalHausdorff_le_of_matches (f '' M) (f '' N) (hM.image hf) (hneM.image f)
    (hN.image hf) (hneN.image f) _
    (mul_nonneg hK (canonicalHausdorff_nonneg M N hM hneM hN hneN))
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨B, hB, hnearest⟩ := spectral_nearest_generator A N hN hneN
    have hdist : spectralNorm (A - B) ≤ canonicalHausdorff M N := by
      rw [← hnearest, ← heq]
      exact pointFamilyDistance_le_hausdorff M N hM hneM hN hneN A hA
    exact ⟨f B, ⟨B, hB, rfl⟩, (hL A (Or.inl hA) B (Or.inr hB)).trans
      (mul_le_mul_of_nonneg_left hdist hK)⟩
  · rintro _ ⟨B, hB, rfl⟩
    obtain ⟨A, hA, hnearest⟩ := spectral_nearest_generator B M hM hneM
    have hdist : spectralNorm (B - A) ≤ canonicalHausdorff M N := by
      rw [← hnearest, ← heq]
      exact (pointFamilyDistance_le_hausdorff N M hN hneN hM hneM B hB).trans_eq
        Metric.hausdorffDist_comm
    exact ⟨f A, ⟨A, hA, rfl⟩, (hL B (Or.inr hB) A (Or.inl hA)).trans
      (mul_le_mul_of_nonneg_left hdist hK)⟩

#print axioms canonicalHausdorff_image_le
#assert_trust kernel canonicalHausdorff_image_le

end NLA.MF06

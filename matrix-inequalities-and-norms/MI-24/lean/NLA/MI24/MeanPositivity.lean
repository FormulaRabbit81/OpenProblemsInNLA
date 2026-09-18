/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Positive definiteness of the concrete means and their sums is proved from
invertible Hermitian congruences. In particular the cross-term sum is positive
because it is the square of the positive sum of the two actual square roots.
-/
import NLA.MI24.SpectralPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma geometric_inner_posDef {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    (spectralPower A (-1 / 2) * B * spectralPower A (-1 / 2)).PosDef := by
  exact posDef_hermitian_sandwich B (spectralPower A (-1 / 2)) hB
    (spectralPower_isHermitian A hA _) (spectralPower_isUnit A hA _)

lemma geometricMean_posDef {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) : (geometricMean A B).PosDef := by
  unfold geometricMean
  exact posDef_hermitian_sandwich _ _
    (spectralPower_posDef _ (geometric_inner_posDef A B hA hB) _)
    (spectralPower_isHermitian A hA _) (spectralPower_isUnit A hA _)

lemma lin_inner_posDef {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    (spectralPower B (1 / 2) * spectralPower A (-1) *
      spectralPower B (1 / 2)).PosDef := by
  exact posDef_hermitian_sandwich _ _ (spectralPower_posDef A hA _)
    (spectralPower_isHermitian B hB _) (spectralPower_isUnit B hB _)

lemma linQuantity_posDef {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) : (linQuantity A B).PosDef := by
  unfold linQuantity
  exact posDef_hermitian_sandwich _ _
    (spectralPower_posDef _ (lin_inner_posDef A B hA hB) _)
    (spectralPower_isHermitian A hA _) (spectralPower_isUnit A hA _)

lemma heron_cross_sum_eq_square {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    A + B + heronCross A B =
      (spectralPower A (1 / 2) + spectralPower B (1 / 2)) *
        (spectralPower A (1 / 2) + spectralPower B (1 / 2)) := by
  unfold heronCross
  rw [add_mul, mul_add, mul_add, spectralPower_half_mul_self A hA,
    spectralPower_half_mul_self B hB]
  abel

lemma heron_cross_sum_posDef {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) : (A + B + heronCross A B).PosDef := by
  have hs : (spectralPower A (1 / 2) + spectralPower B (1 / 2)).PosDef :=
    (spectralPower_posDef A hA _).add (spectralPower_posDef B hB _)
  rw [heron_cross_sum_eq_square A B hA hB]
  simpa only [mul_one] using posDef_hermitian_sandwich
    (1 : Mat n) _ Matrix.PosDef.one hs.isHermitian hs.isUnit

theorem matrix_means_posdef {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    (geometricMean A B).PosDef ∧ (linQuantity A B).PosDef ∧
    (powerHalfP A B).PosDef ∧ (powerHalfQ A B).PosDef ∧
    (heronEndpoint A B).PosDef ∧ (A + B + heronCross A B).PosDef ∧
    (middleMatrix A B).PosDef ∧ (rightMatrix A B).PosDef := by
  have hg := geometricMean_posDef A B hA hB
  have hl := linQuantity_posDef A B hA hB
  have htwo : (0 : ℂ) < 2 := by norm_num [Complex.lt_def]
  have hquarter : (0 : ℂ) < 1 / 4 := by norm_num [Complex.lt_def]
  have he : (heronEndpoint A B).PosDef := (hA.add hB).add (hg.smul htwo)
  have hc := heron_cross_sum_posDef A B hA hB
  exact ⟨hg, hl, he.smul hquarter, hc.smul hquarter, he, hc,
    ((hA.add hB).add hg).add hl, (hA.add hB).add (hl.smul htwo)⟩

theorem power_half_sqrt_q {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    spectralPower (powerHalfQ A B) (1 / 2) =
      (1 / 2 : ℂ) • (spectralPower A (1 / 2) + spectralPower B (1 / 2)) := by
  have hs : (spectralPower A (1 / 2) + spectralPower B (1 / 2)).PosDef :=
    (spectralPower_posDef A hA _).add (spectralPower_posDef B hB _)
  apply spectralPower_half_unique
  · exact hs.smul (by norm_num [Complex.lt_def])
  · unfold powerHalfQ
    rw [heron_cross_sum_eq_square A B hA hB]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num

end NLA.MI24

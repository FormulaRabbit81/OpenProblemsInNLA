/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The fixed-factor radius comparison reuses MF05's Colbrook-attributed envelope.

Similarity is the literal map A -> R*A*Q for the prescribed inverse pair.
The bundled monoid homomorphism preserves chronological products, and an
actual word preimage gives both norm comparisons. Compactness, radius and
product boundedness are proved properties of the actual image families.
-/
import NLA.MF06.WordImages
import NLA.MF06.GrowthComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma conjugateFamily_isCompact {d : ℕ} (Q R : Square d)
    (M : Set (Square d)) (hM : IsCompact M) : IsCompact (conjugateFamily Q R M) :=
  hM.image ((continuous_const.mul continuous_id).mul continuous_const)

lemma conjugateFamily_nonempty {d : ℕ} (Q R : Square d)
    (M : Set (Square d)) (hneM : M.Nonempty) : (conjugateFamily Q R M).Nonempty := hneM.image _

def conjugationMonoidHom {d : ℕ} (Q R : Square d)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) : Square d →* Square d where
  toFun A := R * A * Q
  map_one' := by rw [mul_one, hRQ]
  map_mul' A B := by
    symm
    calc
      (R * A * Q) * (R * B * Q) = R * A * (Q * R) * B * Q := by noncomm_ring
      _ = R * (A * B) * Q := by rw [hQR, mul_one]; noncomm_ring

lemma conjugation_inverse {d : ℕ} (Q R : Square d) (hQR : Q * R = 1) (A : Square d) :
    Q * (R * A * Q) * R = A := by
  calc
    Q * (R * A * Q) * R = (Q * R) * A * (Q * R) := by noncomm_ring
    _ = A := by rw [hQR, one_mul, mul_one]

lemma conjugateFamily_inverse {d : ℕ} (Q R : Square d) (hQR : Q * R = 1)
    (M : Set (Square d)) : conjugateFamily R Q (conjugateFamily Q R M) = M := by
  ext A
  constructor
  · rintro ⟨B, ⟨D, hD, rfl⟩, rfl⟩
    simpa only [conjugation_inverse Q R hQR] using hD
  · intro hA
    exact ⟨R * A * Q, ⟨A, hA, rfl⟩, conjugation_inverse Q R hQR A⟩

lemma spectralNorm_conjugation_le {d : ℕ} (Q R A : Square d) :
    spectralNorm (R * A * Q) ≤ (1 + spectralNorm R * spectralNorm Q) * spectralNorm A := by
  calc
    spectralNorm (R * A * Q) ≤ (spectralNorm R * spectralNorm A) * spectralNorm Q :=
      (spectralNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (spectralNorm_mul_le R A) (spectralNorm_nonneg Q))
    _ = (spectralNorm R * spectralNorm Q) * spectralNorm A := by ring
    _ ≤ (1 + spectralNorm R * spectralNorm Q) * spectralNorm A :=
      mul_le_mul_of_nonneg_right (by linarith) (spectralNorm_nonneg A)

lemma familyGrowth_conjugate_le {d : ℕ} (Q R : Square d)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (n : ℕ) :
    familyGrowth (conjugateFamily Q R M) n ≤
      (1 + spectralNorm R * spectralNorm Q) * familyGrowth M n := by
  have hc := conjugateFamily_isCompact Q R M hM
  have hne := conjugateFamily_nonempty Q R M hneM
  obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained (conjugateFamily Q R M) hc hne n
  obtain ⟨v, hv, rfl⟩ := word_image_preimage M (fun A => R * A * Q) w hword
  have hvn : v.length = n := by simpa only [List.length_map] using hw
  have hproduct : matrixProduct (v.map (fun A => R * A * Q)) = R * matrixProduct v * Q :=
    matrixProduct_map_monoidHom (conjugationMonoidHom Q R hQR hRQ) v
  have hfactor : 0 ≤ 1 + spectralNorm R * spectralNorm Q :=
    add_nonneg zero_le_one (mul_nonneg (spectralNorm_nonneg R) (spectralNorm_nonneg Q))
  rw [← he, hproduct]
  exact (spectralNorm_conjugation_le Q R (matrixProduct v)).trans
    (mul_le_mul_of_nonneg_left (word_le_familyGrowth M hM n v hvn hv) hfactor)

lemma radius_conjugate_le {d : ℕ} (hd : 1 ≤ d) (Q R : Square d)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) :
    jointSpectralRadius (conjugateFamily Q R M) ≤ jointSpectralRadius M := by
  have hfactor : 1 ≤ 1 + spectralNorm R * spectralNorm Q :=
    le_add_of_nonneg_right (mul_nonneg (spectralNorm_nonneg R) (spectralNorm_nonneg Q))
  exact radius_le_of_growth_comparison hd hd M (conjugateFamily Q R M) hM hneM
    (conjugateFamily_isCompact Q R M hM) (conjugateFamily_nonempty Q R M hneM)
    (1 + spectralNorm R * spectralNorm Q) hfactor (familyGrowth_conjugate_le Q R hQR hRQ M hM hneM)

lemma conjugate_product_bounded {d : ℕ} (Q R : Square d)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    IsProductBounded (conjugateFamily Q R M) := by
  have hfactor : 1 ≤ 1 + spectralNorm R * spectralNorm Q :=
    le_add_of_nonneg_right (mul_nonneg (spectralNorm_nonneg R) (spectralNorm_nonneg Q))
  exact product_bounded_of_growth_comparison M (conjugateFamily Q R M)
    (1 + spectralNorm R * spectralNorm Q) hfactor
    (familyGrowth_conjugate_le Q R hQR hRQ M hM hneM) hbounded

/-- C16: actual similarity preserves compactness, radius and product boundedness. -/
theorem similarity_semantics {d : ℕ} (hd : 1 ≤ d) (Q R : Square d)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) :
    IsCompact (conjugateFamily Q R M) ∧ (conjugateFamily Q R M).Nonempty ∧
    jointSpectralRadius (conjugateFamily Q R M) = jointSpectralRadius M ∧
    (IsProductBounded (conjugateFamily Q R M) ↔ IsProductBounded M) := by
  have hc := conjugateFamily_isCompact Q R M hM
  have hne := conjugateFamily_nonempty Q R M hneM
  refine ⟨hc, hne, ?_, ?_⟩
  · apply le_antisymm (radius_conjugate_le hd Q R hQR hRQ M hM hneM)
    have hreverse := radius_conjugate_le hd R Q hRQ hQR (conjugateFamily Q R M) hc hne
    simpa only [conjugateFamily_inverse Q R hQR M] using hreverse
  · constructor
    · intro hbounded
      have hreverse := conjugate_product_bounded R Q hRQ hQR (conjugateFamily Q R M) hc hne hbounded
      simpa only [conjugateFamily_inverse Q R hQR M] using hreverse
    · exact conjugate_product_bounded Q R hQR hRQ M hM hneM

#print axioms similarity_semantics
#assert_trust kernel similarity_semantics

end NLA.MF06

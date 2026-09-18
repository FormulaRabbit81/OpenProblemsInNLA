/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The symbolic interspersed estimate is reused from the Colbrook-attributed MF07
proof, and arbitrary-radius growth semantics from the unchanged MF05 proof.

A fixed similarity shrinks the strict upper blocks. The actual diagonal word
envelope and the existing interspersed estimate control the resulting words.
Letting the positive damping parameter be arbitrarily small proves the exact
triangular radius formula, including zero diagonal radii and all word lengths.
-/
import NLA.MF06.BlockScaling

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma radius_le_block_envelope_rate {d r : ℕ} (hd : 1 ≤ d) (b : Fin d → Fin r)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (K a L t : ℝ) (hK : 1 ≤ K) (ha : 0 < a) (hL : 0 ≤ L)
    (hML : ∀ A ∈ M, spectralNorm A ≤ L) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : ∀ w : List (Square d), WordIn M w →
      spectralNorm (matrixProduct (w.map (blockDiagonalPart b))) ≤ K * a ^ w.length) :
    jointSpectralRadius M ≤ a + K * ((d : ℝ) * L * t) := by
  have hN := blockConjugate_semantics hd b t ht M hM hneM
  have hv : 0 ≤ (d : ℝ) * L * t :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hL) ht.le
  have hrate : 0 < a + K * ((d : ℝ) * L * t) :=
    lt_of_lt_of_le ha (le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hK) hv))
  have hE : ∀ A ∈ M,
      spectralNorm (blockConjugate b t A - blockDiagonalPart b A) ≤ (d : ℝ) * L * t := by
    intro A hA
    exact blockConjugate_error_norm b t ht ht1 A (hupper A hA) L hL (hML A hA)
  have hmap : (fun A : Square d => blockDiagonalPart b A +
      (blockConjugate b t A - blockDiagonalPart b A)) = blockConjugate b t := by
    funext A
    abel
  have hg : ∀ n, familyGrowth ((blockConjugate b t) '' M) n ≤
      K * (a + K * ((d : ℝ) * L * t)) ^ n := by
    intro n
    obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained ((blockConjugate b t) '' M)
      hN.1 hN.2.1 n
    obtain ⟨v, hvM, rfl⟩ := word_image_preimage M (blockConjugate b t) w hword
    have hvn : v.length = n := by simpa only [List.length_map] using hw
    have hwordbound := interspersed_positive_rate M (blockDiagonalPart b)
      (fun A => blockConjugate b t A - blockDiagonalPart b A)
      K a ((d : ℝ) * L * t) hK ha hv hC hE v hvM
    rw [hmap] at hwordbound
    rw [← he]
    simpa only [hvn] using hwordbound
  have hbound := exponential_bound_controls_radius hd ((blockConjugate b t) '' M)
    hN.1 hN.2.1 K (a + K * ((d : ℝ) * L * t)) hK hrate hg
  rw [hN.2.2] at hbound
  exact hbound

/-- C12. The exact finite-block triangular radius formula. -/
theorem block_radius_formula {d r : ℕ} (hd : 1 ≤ d) (b : Fin d → Fin r)
    (hb : Function.Surjective b) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A) :
    jointSpectralRadius M =
      sSup (Set.range (fun i : Fin r => jointSpectralRadius (diagonalFamily b i M))) := by
  have hlower := diagonal_sup_radius_le hd b hb M hM hneM hupper
  apply le_antisymm ?_ hlower
  by_contra hnot
  let s : ℝ := sSup (Set.range (fun i : Fin r => jointSpectralRadius (diagonalFamily b i M)))
  have hsr : s < jointSpectralRadius M := lt_of_not_ge hnot
  have hbounded : BddAbove (Set.range (fun i : Fin r =>
      jointSpectralRadius (diagonalFamily b i M))) := by
    refine ⟨jointSpectralRadius M, ?_⟩
    rintro z ⟨i, rfl⟩
    exact diagonal_radius_le hd b hb i M hM hneM hupper
  have his (i : Fin r) : jointSpectralRadius (diagonalFamily b i M) ≤ s :=
    le_csSup hbounded ⟨i, rfl⟩
  have hs0 : 0 ≤ s :=
    (jointSpectralRadius_nonneg (diagonalFamily b (b ⟨0, hd⟩) M)
      (diagonalFamily_isCompact b (b ⟨0, hd⟩) M hM)
      (diagonalFamily_nonempty b (b ⟨0, hd⟩) M hneM)).trans (his (b ⟨0, hd⟩))
  obtain ⟨a, hsa, har⟩ := exists_between hsr
  have ha : 0 < a := hs0.trans_lt hsa
  obtain ⟨K, hK, hC⟩ := blockDiagonal_exponential_envelope hd b hb M hM hneM a ha
    (fun i => (his i).trans_lt hsa)
  obtain ⟨hL, _, hML⟩ := family_norm_maximum hd M hM hneM
  have hcoefficient : 0 ≤ K * (d : ℝ) * familyNorm M :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hK) (Nat.cast_nonneg d)) hL
  obtain ⟨t0, ht0, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr har)
    (K * (d : ℝ) * familyNorm M)
  let t : ℝ := min t0 1
  have ht : 0 < t := lt_min ht0 zero_lt_one
  have ht1 : t ≤ 1 := min_le_right t0 1
  have ht0le : t ≤ t0 := min_le_left t0 1
  have hsmallt : K * ((d : ℝ) * familyNorm M * t) < jointSpectralRadius M - a := by
    calc
      K * ((d : ℝ) * familyNorm M * t) = (K * (d : ℝ) * familyNorm M) * t := by ring
      _ ≤ (K * (d : ℝ) * familyNorm M) * t0 :=
        mul_le_mul_of_nonneg_left ht0le hcoefficient
      _ < jointSpectralRadius M - a := hsmall
  have hupperRate := radius_le_block_envelope_rate hd b M hM hneM hupper
    K a (familyNorm M) t hK ha hL hML ht ht1 hC
  linarith only [hsmallt, hupperRate]

#print axioms block_radius_formula
#assert_trust kernel block_radius_formula

end NLA.MF06

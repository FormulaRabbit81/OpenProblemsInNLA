/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The reused general envelope retains Matthew J. Colbrook's MF05 attribution.

Actual compound words obey a fixed-factor power bound. A positive exponential
discount and continuity remove that fixed factor, even at zero radius and
degree zero; no numerical root or interval enumeration is needed.
-/
import NLA.MF06.AllocationProducts
import NLA.MF06.GrowthComparison

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

def compoundMonoidHom (d k : ℕ) : Square d →* Square (compoundDim d k) where
  toFun := compoundMatrix k
  map_one' := (compound_algebra k 1 1).1
  map_mul' A B := (compound_algebra k A B).2.1

lemma compound_word_product {d : ℕ} (k : ℕ) (w : List (Square d)) :
    matrixProduct (w.map (compoundMatrix k)) = compoundMatrix k (matrixProduct w) :=
  matrixProduct_map_monoidHom (compoundMonoidHom d k) w

lemma compound_radius_le_power {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (k : ℕ) (hk : k ≤ d) :
    jointSpectralRadius (compoundFamily k M) ≤ jointSpectralRadius M ^ k := by
  have hcompact : IsCompact (compoundFamily k M) := hM.image (continuous_compoundMatrix k)
  have hnonempty : (compoundFamily k M).Nonempty := hneM.image _
  have hdim := (compound_dimensions d k).2 hk
  have hC : 0 < compoundNormConstant d k := (compound_norm_bound k hk (1 : Square d)).1
  have hupper (a : ℝ) (ha : jointSpectralRadius M < a) :
      jointSpectralRadius (compoundFamily k M) ≤ a ^ k := by
    obtain ⟨ha0, K, hK, hbound⟩ := general_exponential_envelope hd M hM hneM a ha
    let D := max 1 (compoundNormConstant d k * K ^ k)
    apply exponential_bound_controls_radius hdim (compoundFamily k M) hcompact hnonempty
      D (a ^ k) (le_max_left _ _) (pow_pos ha0 k)
    intro n
    obtain ⟨w, hwlen, hw, he⟩ := familyGrowth_attained (compoundFamily k M) hcompact hnonempty n
    obtain ⟨v, hv, rfl⟩ := word_image_preimage M (compoundMatrix k) w hw
    have hlen : v.length = n := by simpa only [List.length_map] using hwlen
    have hP : spectralNorm (matrixProduct v) ≤ K * a ^ n :=
      (word_le_familyGrowth M hM n v hlen hv).trans (hbound n)
    rw [← he, compound_word_product]
    calc
      spectralNorm (compoundMatrix k (matrixProduct v)) ≤
          compoundNormConstant d k * spectralNorm (matrixProduct v) ^ k :=
        (compound_norm_bound k hk _).2
      _ ≤ compoundNormConstant d k * (K * a ^ n) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (spectralNorm_nonneg _) hP k) hC.le
      _ = (compoundNormConstant d k * K ^ k) * (a ^ k) ^ n := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n k, mul_assoc]
      _ ≤ D * (a ^ k) ^ n :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (pow_nonneg ha0.le k) n)
  have hlim : Tendsto (fun a : ℝ => a ^ k) (𝓝[>] jointSpectralRadius M)
      (𝓝 (jointSpectralRadius M ^ k)) :=
    (continuous_id.pow k).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact hupper a ha

#print axioms compound_radius_le_power
#assert_trust kernel compound_radius_le_power

end NLA.MF06

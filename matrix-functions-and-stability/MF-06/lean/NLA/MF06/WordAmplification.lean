/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The actual-radius exponential envelope retains the attribution to Matthew J.
Colbrook in the unchanged MF05 development.

Uniform amplification by words of bounded length builds legal trajectories.
Such amplification by a factor above one contradicts actual joint radius one.
Only a fixed natural power is made close to one; no numerical root evaluation
or word enumeration is used.
-/
import NLA.MF06.Definitions
import NLA.MF05.GeneralEnvelope
import NLA.MF07.NormGeometry
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
open Filter Topology

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma bounded_word_trajectory {d : ℕ} (M : Set (Square d)) (ell : ℕ)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hstep : ∀ x : EuclideanVector d, ∃ w : List (Square d), WordIn M w ∧
      w.length ≤ ell ∧ γ * ‖x‖ ≤ ‖applyMatrix (matrixProduct w) x‖)
    (x₀ : EuclideanVector d) (n : ℕ) :
    ∃ w : List (Square d), WordIn M w ∧ w.length ≤ n * ell ∧
      γ ^ n * ‖x₀‖ ≤ ‖applyMatrix (matrixProduct w) x₀‖ := by
  induction n with
  | zero =>
      refine ⟨[], WordIn_nil M, by simp only [List.length_nil, zero_mul, le_refl], ?_⟩
      simp only [pow_zero, one_mul, matrixProduct_nil, applyMatrix_one, le_refl]
  | succ n ih =>
      obtain ⟨v, hv, hvlength, hvgrowth⟩ := ih
      obtain ⟨w, hw, hwlength, hwgrowth⟩ := hstep (applyMatrix (matrixProduct v) x₀)
      refine ⟨v ++ w, (WordIn_append_iff M v w).mpr ⟨hv, hw⟩, ?_, ?_⟩
      · calc
          (v ++ w).length = v.length + w.length := List.length_append
          _ ≤ n * ell + ell := Nat.add_le_add hvlength hwlength
          _ = (n + 1) * ell := by rw [Nat.add_mul, Nat.one_mul]
      · rw [matrixProduct_append, applyMatrix_mul, pow_succ']
        simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hvgrowth hγ).trans hwgrowth

lemma exists_one_lt_power_lt (ell : ℕ) (γ : ℝ) (hγ : 1 < γ) :
    ∃ a : ℝ, 1 < a ∧ a ^ ell < γ := by
  have hc : Continuous (fun a : ℝ => a ^ ell) := continuous_id.pow ell
  have hfull : Tendsto (fun a : ℝ => a ^ ell) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) ^ ell)) :=
    hc.tendsto 1
  have ht : Tendsto (fun a : ℝ => a ^ ell) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [one_pow] using
      hfull.mono_left (show (𝓝[>] (1 : ℝ)) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] (1 : ℝ), a ^ ell < γ :=
    ht.eventually (gt_mem_nhds hγ)
  obtain ⟨a, ha, ha1⟩ := (hsmall.and self_mem_nhdsWithin).exists
  exact ⟨a, ha1, ha⟩

lemma bounded_word_amplification_contradiction {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hradius : jointSpectralRadius M = 1) (ell : ℕ) (γ : ℝ) (hγ : 1 < γ)
    (hstep : ∀ x : EuclideanVector d, ∃ w : List (Square d), WordIn M w ∧
      w.length ≤ ell ∧ γ * ‖x‖ ≤ ‖applyMatrix (matrixProduct w) x‖) : False := by
  obtain ⟨a, ha1, hapower⟩ := exists_one_lt_power_lt ell γ hγ
  have ha : 0 < a := zero_lt_one.trans ha1
  have hγ0 : 0 < γ := zero_lt_one.trans hγ
  obtain ⟨_, K, hK, hbound⟩ := general_exponential_envelope hd M hM hneM a
    (by simpa only [hradius] using ha1)
  let x₀ : EuclideanVector d := coordinateUnit ⟨0, hd⟩
  have hx₀ : ‖x₀‖ = 1 := coordinateUnit_norm _
  have hgrowth (n : ℕ) : γ ^ n ≤ K * (a ^ ell) ^ n := by
    obtain ⟨w, hw, hwlength, hwgrowth⟩ := bounded_word_trajectory M ell γ hγ0.le hstep x₀ n
    have hnorm : γ ^ n ≤ ‖applyMatrix (matrixProduct w) x₀‖ := by
      simpa only [hx₀, mul_one] using hwgrowth
    calc
      γ ^ n ≤ ‖applyMatrix (matrixProduct w) x₀‖ := hnorm
      _ ≤ spectralNorm (matrixProduct w) := by
        simpa only [hx₀, mul_one] using norm_applyMatrix_le (matrixProduct w) x₀
      _ ≤ familyGrowth M w.length := word_le_familyGrowth M hM w.length w rfl hw
      _ ≤ K * a ^ w.length := hbound w.length
      _ ≤ K * a ^ (n * ell) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha1.le hwlength) (zero_le_one.trans hK)
      _ = K * (a ^ ell) ^ n := by rw [Nat.mul_comm n ell, pow_mul]
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hK0)
    ((div_lt_one hγ0).mpr hapower)
  have hratio : K * (a ^ ell / γ) ^ n < 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hK0).mp hn
  have hdiv : (K * (a ^ ell) ^ n) / γ ^ n < 1 := by
    simpa only [div_pow, mul_div_assoc] using hratio
  have hstrict : K * (a ^ ell) ^ n < γ ^ n := (div_lt_one (pow_pos hγ0 n)).mp hdiv
  exact (not_lt_of_ge (hgrowth n)) hstrict

#print axioms bounded_word_amplification_contradiction
#assert_trust kernel bounded_word_amplification_contradiction

end NLA.MF06

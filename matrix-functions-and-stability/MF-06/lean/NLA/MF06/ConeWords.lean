/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The imported root-infimum exponential envelope retains MF05's Colbrook attribution.

Finite induction appends the chosen generator to an actual chronological
word. A fixed positive coefficient in a lower exponential growth estimate
does not change the actual joint spectral radius. The latter assertion uses
the proved all-word exponential envelope above the actual root infimum and
geometric decay, avoiding any extra real-root interval computation.
-/
import NLA.MF05.GeneralEnvelope
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
open Filter Topology

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma cone_trajectory_words {d : ℕ} (N : Set (Square d))
    (a b : EuclideanVector d → ℝ) (H γ : ℝ) (hγ : 0 ≤ γ)
    (hstep : ∀ x : EuclideanVector d, a x ≤ H * b x → 0 < b x →
      ∃ B ∈ N, a (applyMatrix B x) ≤ H * b (applyMatrix B x) ∧
        γ * b x ≤ b (applyMatrix B x) ∧ 0 < b (applyMatrix B x))
    (x₀ : EuclideanVector d) (hstart : a x₀ ≤ H * b x₀) (hstartb : b x₀ = 1) :
    ∀ n : ℕ, ∃ w : List (Square d), w.length = n ∧ WordIn N w ∧
      a (applyMatrix (matrixProduct w) x₀) ≤ H * b (applyMatrix (matrixProduct w) x₀) ∧
      γ ^ n ≤ b (applyMatrix (matrixProduct w) x₀) ∧
      0 < b (applyMatrix (matrixProduct w) x₀) := by
  intro n
  induction n with
  | zero =>
      refine ⟨[], rfl, WordIn_nil N, ?_, ?_, ?_⟩
      · simpa only [matrixProduct_nil, applyMatrix_one] using hstart
      · simpa only [matrixProduct_nil, applyMatrix_one, pow_zero] using hstartb.ge
      · simpa only [matrixProduct_nil, applyMatrix_one, hstartb] using (zero_lt_one : (0 : ℝ) < 1)
  | succ n ih =>
      obtain ⟨w, hw, hword, hcone, hgrowth, hpositive⟩ := ih
      obtain ⟨B, hB, hnewcone, hnewgrowth, hnewpositive⟩ :=
        hstep (applyMatrix (matrixProduct w) x₀) hcone hpositive
      have hlength : (w ++ [B]).length = n + 1 := by
        simp only [List.length_append, List.length_singleton, hw]
      have hword' : WordIn N (w ++ [B]) := (WordIn_append_iff N w [B]).mpr
        ⟨hword, (WordIn_cons_iff N B []).mpr ⟨hB, WordIn_nil N⟩⟩
      have haction : applyMatrix (matrixProduct (w ++ [B])) x₀ =
          applyMatrix B (applyMatrix (matrixProduct w) x₀) := by
        rw [(matrix_product_semantics (d := d)).2 w B, applyMatrix_mul]
      refine ⟨w ++ [B], hlength, hword', ?_, ?_, ?_⟩
      · simpa only [haction] using hnewcone
      · rw [haction, pow_succ']
        exact (mul_le_mul_of_nonneg_left hgrowth hγ).trans hnewgrowth
      · simpa only [haction] using hnewpositive

lemma radius_ge_of_exponential_lower_bound {d : ℕ} (hd : 1 ≤ d)
    (N : Set (Square d)) (hN : IsCompact N) (hneN : N.Nonempty)
    (D γ : ℝ) (hD : 1 ≤ D) (hγ : 0 < γ)
    (hlower : ∀ n : ℕ, γ ^ n ≤ D * familyGrowth N n) :
    γ ≤ jointSpectralRadius N := by
  by_contra hnot
  obtain ⟨a, hra, haγ⟩ := exists_between (lt_of_not_ge hnot)
  obtain ⟨ha, K, hK, hupper⟩ := general_exponential_envelope hd N hN hneN a hra
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hDK : 0 < D * K := mul_pos (zero_lt_one.trans_le hD) (zero_lt_one.trans_le hK)
  have hdecay : Tendsto (fun n : ℕ => (a / γ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha.le hγ.le)
      ((div_lt_one hγ).mpr haγ)
  have hsmall : ∀ᶠ n : ℕ in atTop, (a / γ) ^ n < 1 / (D * K) :=
    hdecay.eventually (gt_mem_nhds (one_div_pos.mpr hDK))
  obtain ⟨n, hn⟩ := hsmall.exists
  have hratio : (D * K) * (a / γ) ^ n < 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hDK).mp hn
  have hdiv : ((D * K) * a ^ n) / γ ^ n < 1 := by
    simpa only [div_pow, mul_div_assoc] using hratio
  have hstrict : (D * K) * a ^ n < γ ^ n := (div_lt_one (pow_pos hγ n)).mp hdiv
  have hbound : γ ^ n ≤ (D * K) * a ^ n := by
    calc
      γ ^ n ≤ D * familyGrowth N n := hlower n
      _ ≤ D * (K * a ^ n) := mul_le_mul_of_nonneg_left (hupper n) hD0
      _ = (D * K) * a ^ n := (mul_assoc _ _ _).symm
  exact (not_lt_of_ge hbound) hstrict

#print axioms cone_trajectory_words
#assert_trust kernel cone_trajectory_words
#print axioms radius_ge_of_exponential_lower_bound
#assert_trust kernel radius_ge_of_exponential_lower_bound

end NLA.MF06

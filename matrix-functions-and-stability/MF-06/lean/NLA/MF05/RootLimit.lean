/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original discounted-word growth argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Lemma 3 and Corollary 7.

The actual positive-index-root infimum is the root limit at arbitrary radius.
The accepted finite-block envelope supplies an eventual upper bound; the
infimum supplies the lower bound. The geometric decay argument never takes
the logarithm of word growth, so zero growth and zero radius remain included.
-/
import NLA.MF05.GeneralEnvelope
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter

noncomputable section
namespace NLA.MF05
open NLA.MF07

/-- A fixed positive coefficient is absorbed by any larger positive discount.
The threshold `1 / K` turns geometric decay into a strict word-growth bound;
positive-index power monotonicity then gives the root bound. -/
lemma eventually_rootGrowth_lt_of_exponential_bound {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (K a b : ℝ)
    (hK : 0 < K) (ha : 0 < a) (hab : a < b)
    (hbound : ∀ n : ℕ, familyGrowth M n ≤ K * a ^ n) :
    ∀ᶠ n : ℕ in atTop, rootGrowth M n < b := by
  have hb : 0 < b := ha.trans hab
  have hdecay : Tendsto (fun n : ℕ => (a / b) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha.le hb.le)
      ((div_lt_one hb).mpr hab)
  have htail : ∀ᶠ n : ℕ in atTop, (a / b) ^ n < 1 / K :=
    hdecay.eventually (gt_mem_nhds (one_div_pos.mpr hK))
  filter_upwards [htail, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  have hdiscount : K * (a / b) ^ n < 1 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hK).mp hn
  have hscaled : (K * a ^ n) / b ^ n < 1 := by
    simpa only [div_pow, mul_div_assoc] using hdiscount
  have hword : familyGrowth M n < b ^ n :=
    (hbound n).trans_lt ((div_lt_one (pow_pos hb n)).mp hscaled)
  apply (pow_lt_pow_iff_left₀ (n := n)
    (rootGrowth_nonneg M hM hne n) hb.le (by omega)).mp
  rw [rootGrowth_pow M hM hne n hnpos]
  exact hword

theorem general_root_limit_semantics {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    0 ≤ jointSpectralRadius M ∧ jointSpectralRadius M ≤ familyNorm M ∧
    Tendsto (rootGrowth M) atTop (𝓝 (jointSpectralRadius M)) := by
  have hnorm : jointSpectralRadius M ≤ familyNorm M := by
    simpa only [rootGrowth, Real.rpow_eq_pow, Nat.cast_one, div_one, Real.rpow_one,
      familyGrowth_one hd M hM hne] using
      jointSpectralRadius_le_root M hM hne 1 (by omega)
  refine ⟨jointSpectralRadius_nonneg M hM hne, hnorm, tendsto_order.mpr ?_⟩
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ha.trans_le (jointSpectralRadius_le_root M hM hne n hn)
  · intro b hb
    obtain ⟨a, hra, hab⟩ := exists_between hb
    obtain ⟨ha, K, hK, hbound⟩ := general_exponential_envelope hd M hM hne a hra
    exact eventually_rootGrowth_lt_of_exponential_bound M hM hne K a b
      (lt_of_lt_of_le zero_lt_one hK) ha hab hbound

theorem exponential_bound_controls_radius {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (K b : ℝ) (hK : 1 ≤ K) (hb : 0 < b)
    (hbound : ∀ n : ℕ, familyGrowth M n ≤ K * b ^ n) :
    jointSpectralRadius M ≤ b := by
  by_contra hnot
  obtain ⟨c, hbc, hcr⟩ := exists_between (lt_of_not_ge hnot)
  have hupper := eventually_rootGrowth_lt_of_exponential_bound M hM hne K b c
    (lt_of_lt_of_le zero_lt_one hK) hb hbc hbound
  have hlower := (general_root_limit_semantics hd M hM hne).2.2.eventually
    (lt_mem_nhds hcr)
  obtain ⟨n, hnlo, hnhi⟩ := (hlower.and hupper).exists
  exact (not_lt_of_ge hnlo.le) hnhi

#print axioms general_root_limit_semantics
#assert_trust kernel general_root_limit_semantics
#print axioms exponential_bound_controls_radius
#assert_trust kernel exponential_bound_controls_radius

end NLA.MF05

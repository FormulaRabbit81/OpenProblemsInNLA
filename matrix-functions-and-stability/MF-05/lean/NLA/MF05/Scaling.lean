/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Proposition 5.

Positive scalar multiplication acts on every actual generator and word.
Compact attainment proves the growth equality without exchanging abstract
suprema. The general root limit then identifies the scaled radius, including
zero radius. All dimensions and word lengths are symbolic.
-/
import NLA.MF05.RootLimit
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter

noncomputable section
namespace NLA.MF05
open NLA.MF07

lemma scaledFamily_isCompact {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (c : ℝ) : IsCompact (scaledFamily c M) :=
  hM.image (continuous_const_smul (c : ℂ))

lemma scaledFamily_nonempty {d : ℕ} (M : Set (Square d)) (hne : M.Nonempty)
    (c : ℝ) : (scaledFamily c M).Nonempty := hne.image _

lemma scaled_word_in {d : ℕ} (M : Set (Square d)) (c : ℝ)
    (w : List (Square d)) (hw : WordIn M w) :
    WordIn (scaledFamily c M) (w.map (fun A => (c : ℂ) • A)) := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  exact ⟨A, hw A hA, rfl⟩

/-- Every word in the scaled family has a word preimage with the same order.
This proof does not invert the scalar or assume distinct generators. -/
lemma scaled_word_preimage {d : ℕ} (M : Set (Square d)) (c : ℝ)
    (w : List (Square d)) (hw : WordIn (scaledFamily c M) w) :
    ∃ v : List (Square d), WordIn M v ∧ w = v.map (fun A => (c : ℂ) • A) := by
  induction w with
  | nil => exact ⟨[], WordIn_nil M, rfl⟩
  | cons A w ih =>
      obtain ⟨hA, htail⟩ := (WordIn_cons_iff (scaledFamily c M) A w).mp hw
      obtain ⟨B, hB, rfl⟩ := hA
      obtain ⟨v, hv, rfl⟩ := ih htail
      exact ⟨B :: v, (WordIn_cons_iff M B v).mpr ⟨hB, hv⟩, rfl⟩

lemma scaled_word_product {d : ℕ} (c : ℂ) (w : List (Square d)) :
    matrixProduct (w.map (fun A => c • A)) = c ^ w.length • matrixProduct w := by
  simpa only [matrixProduct, List.length_reverse, ← List.map_reverse] using
    (List.smul_prod w.reverse c).symm

lemma scaled_word_norm {d : ℕ} (c : ℝ) (hc : 0 < c) (w : List (Square d)) :
    spectralNorm (matrixProduct (w.map (fun A => (c : ℂ) • A))) =
      c ^ w.length * spectralNorm (matrixProduct w) := by
  rw [scaled_word_product, spectralNorm_smul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]

lemma familyGrowth_scaled {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) (c : ℝ) (hc : 0 < c) (n : ℕ) :
    familyGrowth (scaledFamily c M) n = c ^ n * familyGrowth M n := by
  have hsM := scaledFamily_isCompact M hM c
  have hsne := scaledFamily_nonempty M hne c
  apply le_antisymm
  · obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained (scaledFamily c M) hsM hsne n
    obtain ⟨v, hv, rfl⟩ := scaled_word_preimage M c w hword
    have hvn : v.length = n := by simpa only [List.length_map] using hw
    rw [← he, scaled_word_norm c hc v, hvn]
    exact mul_le_mul_of_nonneg_left (word_le_familyGrowth M hM n v hvn hv)
      (pow_nonneg hc.le n)
  · obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained M hM hne n
    have hb := word_le_familyGrowth (scaledFamily c M) hsM n
      (w.map (fun A => (c : ℂ) • A))
      (by simpa only [List.length_map] using hw) (scaled_word_in M c w hword)
    simpa only [scaled_word_norm c hc w, hw, he] using hb

lemma rootGrowth_scaled {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n) :
    rootGrowth (scaledFamily c M) n = c * rootGrowth M n := by
  rw [rootGrowth, familyGrowth_scaled M hM hne c hc n, Real.rpow_eq_pow,
    Real.mul_rpow (pow_nonneg hc.le n) (familyGrowth_nonneg M hM hne n), one_div,
    Real.pow_rpow_inv_natCast hc.le (show n ≠ 0 by omega)]
  simp only [rootGrowth, Real.rpow_eq_pow, one_div]

theorem positive_scaling_semantics {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (c : ℝ) (hc : 0 < c) :
    IsCompact (scaledFamily c M) ∧ (scaledFamily c M).Nonempty ∧
    familyNorm (scaledFamily c M) = c * familyNorm M ∧
    (∀ n : ℕ, familyGrowth (scaledFamily c M) n = c ^ n * familyGrowth M n) ∧
    jointSpectralRadius (scaledFamily c M) = c * jointSpectralRadius M := by
  have hsM := scaledFamily_isCompact M hM c
  have hsne := scaledFamily_nonempty M hne c
  refine ⟨hsM, hsne, ?_, familyGrowth_scaled M hM hne c hc, ?_⟩
  · calc
      familyNorm (scaledFamily c M) = familyGrowth (scaledFamily c M) 1 :=
        (familyGrowth_one hd (scaledFamily c M) hsM hsne).symm
      _ = c * familyNorm M := by
        rw [familyGrowth_scaled M hM hne c hc 1, pow_one, familyGrowth_one hd M hM hne]
  · have horiginal := (general_root_limit_semantics hd M hM hne).2.2.const_mul c
    have hscaled : Tendsto (rootGrowth (scaledFamily c M)) atTop
        (𝓝 (c * jointSpectralRadius M)) := by
      apply horiginal.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact (rootGrowth_scaled M hM hne c hc n hn).symm
    exact tendsto_nhds_unique
      (general_root_limit_semantics hd (scaledFamily c M) hsM hsne).2.2 hscaled

#print axioms positive_scaling_semantics
#assert_trust kernel positive_scaling_semantics

end NLA.MF05

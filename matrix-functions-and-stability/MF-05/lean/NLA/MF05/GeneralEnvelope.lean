/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original discounted-word norm argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Lemma 3 and Corollary 7.

The arbitrary-radius prerequisite is proved directly from the actual root
infimum. One good block controls its repeats; only finitely many remainder
lengths need a common bound. Zero word growth and zero radius need no logarithm.
Published MF07 compact-growth and repeated-block results are reused unchanged.
-/
import NLA.MF05.Definitions
import NLA.MF07.RootSemantics
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

lemma jointSpectralRadius_nonneg {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) : 0 ≤ jointSpectralRadius M := by
  unfold jointSpectralRadius
  apply le_csInf (rootValues_nonempty M)
  rintro r ⟨n, _, rfl⟩
  exact rootGrowth_nonneg M hM hne n

/-- A single block bound yields an envelope for every length. The finite
remainder bound is a real upper bound, with no positivity assumption on growth. -/
lemma exponential_envelope_of_block {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (a : ℝ) (ha : 0 < a)
    (k : ℕ) (hk : 1 ≤ k) (hblock : familyGrowth M k ≤ a ^ k) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, familyGrowth M n ≤ K * a ^ n := by
  obtain ⟨K0, hK0⟩ := (Set.finite_range
    (fun r : Fin k => familyGrowth M (r : ℕ) / a ^ (r : ℕ))).bddAbove
  refine ⟨max 1 K0, le_max_left _ _, ?_⟩
  intro n
  have hr : n % k < k := Nat.mod_lt n (by omega)
  have hrem : familyGrowth M (n % k) ≤ max 1 K0 * a ^ (n % k) := by
    have hratio : familyGrowth M (n % k) / a ^ (n % k) ≤ K0 :=
      hK0 ⟨⟨n % k, hr⟩, rfl⟩
    exact (div_le_iff₀ (pow_pos ha _)).mp (hratio.trans (le_max_right _ _))
  have hblocks : familyGrowth M ((n / k) * k) ≤ a ^ ((n / k) * k) := by
    calc
      familyGrowth M ((n / k) * k) ≤ familyGrowth M k ^ (n / k) :=
        familyGrowth_mul_le_pow hd M hM hne (n / k) k
      _ ≤ (a ^ k) ^ (n / k) :=
        pow_le_pow_left₀ (familyGrowth_nonneg M hM hne k) hblock (n / k)
      _ = a ^ ((n / k) * k) := by rw [← pow_mul, Nat.mul_comm]
  have hdecomp : n = (n / k) * k + n % k := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod n k).symm
  calc
    familyGrowth M n = familyGrowth M ((n / k) * k + n % k) :=
      congrArg (familyGrowth M) hdecomp
    _ ≤ familyGrowth M ((n / k) * k) * familyGrowth M (n % k) :=
      family_growth_submultiplicative hd M hM hne ((n / k) * k) (n % k)
    _ ≤ a ^ ((n / k) * k) * (max 1 K0 * a ^ (n % k)) :=
      mul_le_mul hblocks hrem (familyGrowth_nonneg M hM hne _) (pow_nonneg ha.le _)
    _ = max 1 K0 * a ^ n := by rw [mul_left_comm, ← pow_add, ← hdecomp]

theorem general_exponential_envelope {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (a : ℝ) (ha : jointSpectralRadius M < a) :
    0 < a ∧ ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, familyGrowth M n ≤ K * a ^ n := by
  have ha0 : 0 < a := (jointSpectralRadius_nonneg M hM hne).trans_lt ha
  obtain ⟨r, ⟨k, hk, rfl⟩, hroot⟩ :=
    exists_lt_of_csInf_lt (rootValues_nonempty M) (by
      simpa only [jointSpectralRadius] using ha)
  have hblock : familyGrowth M k ≤ a ^ k := by
    rw [← rootGrowth_pow M hM hne k hk]
    exact pow_le_pow_left₀ (rootGrowth_nonneg M hM hne k) hroot.le k
  exact ⟨ha0, exponential_envelope_of_block hd M hM hne a ha0 k hk hblock⟩

#print axioms jointSpectralRadius_nonneg
#assert_trust kernel jointSpectralRadius_nonneg
#print axioms general_exponential_envelope
#assert_trust kernel general_exponential_envelope

end NLA.MF05

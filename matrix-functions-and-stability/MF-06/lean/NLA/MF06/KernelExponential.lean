/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The reused full-family radius-one lower bound retains the MF07 source authorship.

Uniform convergence on the actual stable kernel yields a contracting length.
Actual restricted word growth is submultiplicative, hence decays exponentially.
If the kernel were the whole space, its contracting length would contradict
the radius-one lower bound for the original full word growth.
-/
import NLA.MF06.RestrictedGrowth
import NLA.MF06.BlockDecay
import NLA.MF07.RootSemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma restrictedGrowth_small_block {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (S : Submodule ℂ (EuclideanVector d))
    (hzero : ∀ x : EuclideanVector d, x ∈ S → stableGauge M x = 0) :
    ∃ N : ℕ, 1 ≤ N ∧ restrictedGrowth M S N ≤ 1 / 2 := by
  obtain ⟨N, hN, hsmall⟩ :=
    uniform_small_tail_on_subspace M hM hneM hbounded S hzero (1 / 2) (by norm_num)
  obtain ⟨_, _, hnorm⟩ := (bounded_envelope_norm M hM hneM hbounded).2.2.1
  refine ⟨N, hN, ?_⟩
  unfold restrictedGrowth
  refine csSup_le (α := ℝ) ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨w, hw, hword, x, hx, hunit, rfl⟩)
  · norm_num
  · calc
      ‖applyMatrix (matrixProduct w) x‖ ≤ boundedEnvelope M (applyMatrix (matrixProduct w) x) :=
        (hnorm _).1
      _ ≤ tailEnvelope M N x := word_le_tailEnvelope M hM hneM hbounded N w hw hword x
      _ ≤ 1 / 2 := hsmall N le_rfl x hx hunit

/-- C08: the actual stable kernel is proper and all its restricted words decay
exponentially. The inserted-zero convention keeps the zero submodule case exact. -/
theorem stable_kernel_exponential {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (hradius : jointSpectralRadius M = 1) :
    ∃ S : Submodule ℂ (EuclideanVector d),
      (∀ x : EuclideanVector d, x ∈ S ↔ stableGauge M x = 0) ∧
      S ≠ ⊤ ∧ FamilyInvariant M S ∧
      ∃ q K : ℝ, 0 < q ∧ q < 1 ∧ 1 ≤ K ∧
        ∀ n : ℕ, restrictedGrowth M S n ≤ K * q ^ n := by
  let S := stableKernel M hM hneM hbounded
  have hzero : ∀ x : EuclideanVector d, x ∈ S ↔ stableGauge M x = 0 := fun _ => Iff.rfl
  have hInv : FamilyInvariant M S := stableKernel_invariant M hM hneM hbounded
  obtain ⟨N, hN, hsmall⟩ := restrictedGrowth_small_block M hM hneM hbounded S
    (fun x hx => (hzero x).mp hx)
  have hproper : S ≠ ⊤ := by
    intro he
    have hsmall' : familyGrowth M N ≤ 1 / 2 := by
      simpa only [he, restrictedGrowth_top M hM hneM] using hsmall
    have hone := familyGrowth_ge_one_of_radius_one hd M hM hneM hradius N
    linarith
  obtain ⟨K, hK, hbound⟩ := hbounded
  obtain ⟨q, hq0, hq1, hdecay⟩ := exponential_decay_of_half_block (restrictedGrowth M S) K hK
    (restrictedGrowth_nonneg M hM hneM S) (restrictedGrowth_zero_le_one M S)
    (restrictedGrowth_submultiplicative M hM hneM S hInv)
    (fun n => (restrictedGrowth_le_familyGrowth M hM hneM S n).trans (hbound n)) N hN hsmall
  refine ⟨S, hzero, hproper, hInv, q, 2 * K, hq0, hq1, ?_, hdecay⟩
  linarith

#print axioms stable_kernel_exponential
#assert_trust kernel stable_kernel_exponential

end NLA.MF06

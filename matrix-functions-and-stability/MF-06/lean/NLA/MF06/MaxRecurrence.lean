/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Each finite tail attains its one-generator recurrence on the entire compact
matrix family. A decreasing sequence of compact sets of admissible generators
then supplies one generator attaining the limiting recurrence. No finite-family
replacement, selected subsequence oracle or strictly positive gauge is assumed.
-/
import NLA.MF06.StableGauge
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 Filter Topology

lemma continuous_applyMatrix_left {d : ℕ} (x : EuclideanVector d) :
    Continuous (fun A : Square d => applyMatrix A x) := by
  let f : Square d →ₗ[ℂ] (EuclideanVector d →L[ℂ] EuclideanVector d) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact f.continuous_of_finiteDimensional.clm_apply continuous_const

/-- Prefixing the chronological word by A puts its action before all n later factors. -/
lemma tailEnvelope_generator_le {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (A : Square d) (hA : A ∈ M) (x : EuclideanVector d) :
    tailEnvelope M n (applyMatrix A x) ≤ tailEnvelope M (n + 1) x := by
  apply csSup_le (tailValues_nonempty M hneM n (applyMatrix A x))
  rintro r ⟨w, hw, hword, rfl⟩
  have hlength : (A :: w).length = n + 1 := by simp only [List.length_cons, hw]
  have hword' : WordIn M (A :: w) := (WordIn_cons_iff M A w).mpr ⟨hA, hword⟩
  simpa only [matrixProduct_cons, applyMatrix_mul] using
    word_le_tailEnvelope M hM hneM hbounded (n + 1) (A :: w) hlength hword' x

/-- A maximum over the actual compact family supplies the finite-tail recurrence. -/
lemma tailEnvelope_succ_maximum {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x : EuclideanVector d) :
    ∃ A ∈ M, tailEnvelope M n (applyMatrix A x) = tailEnvelope M (n + 1) x := by
  have hcont : Continuous (fun A : Square d => tailEnvelope M n (applyMatrix A x)) :=
    (tailEnvelope_continuous M hM hneM hbounded n).comp (continuous_applyMatrix_left x)
  obtain ⟨A, hA, hmax⟩ := hM.exists_isMaxOn hneM hcont.continuousOn
  refine ⟨A, hA, le_antisymm (tailEnvelope_generator_le M hM hneM hbounded n A hA x) ?_⟩
  apply csSup_le (tailValues_nonempty M hneM (n + 1) x)
  rintro r ⟨w, hw, hword, rfl⟩
  cases w with
  | nil => simp at hw
  | cons B w =>
      obtain ⟨hB, hword⟩ := (WordIn_cons_iff M B w).mp hword
      have hlength : w.length = n := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hw
      rw [matrixProduct_cons, applyMatrix_mul]
      exact (word_le_tailEnvelope M hM hneM hbounded n w hlength hword (applyMatrix B x)).trans
        (hmax hB)

lemma stableGauge_le_tailEnvelope {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x : EuclideanVector d) : stableGauge M x ≤ tailEnvelope M n x :=
  (tailEnvelope_antitone M hM hneM hbounded x).le_of_tendsto
    (tailEnvelope_tendsto M hM hneM hbounded x) n

lemma stableGauge_generator_le {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (A : Square d) (hA : A ∈ M) (x : EuclideanVector d) :
    stableGauge M (applyMatrix A x) ≤ stableGauge M x := by
  exact le_of_tendsto_of_tendsto' (tailEnvelope_tendsto M hM hneM hbounded (applyMatrix A x))
    (tailEnvelope_tendsto M hM hneM hbounded x)
    (fun n => (tailEnvelope_generator_le M hM hneM hbounded n A hA x).trans
      (tailEnvelope_succ_le M hM hneM hbounded n x))

/-- C07: one original generator attains the exact limiting max recurrence. -/
theorem stable_gauge_max_recurrence {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    ∀ x : EuclideanVector d,
      (∀ A ∈ M, stableGauge M (applyMatrix A x) ≤ stableGauge M x) ∧
      ∃ A ∈ M, stableGauge M (applyMatrix A x) = stableGauge M x := by
  intro x
  refine ⟨fun A hA => stableGauge_generator_le M hM hneM hbounded A hA x, ?_⟩
  let F : ℕ → Set (Square d) := fun n =>
    M ∩ {A | stableGauge M x ≤ tailEnvelope M n (applyMatrix A x)}
  have hclosed : ∀ n : ℕ,
      IsClosed {A : Square d | stableGauge M x ≤ tailEnvelope M n (applyMatrix A x)} := by
    intro n
    exact isClosed_le continuous_const
      ((tailEnvelope_continuous M hM hneM hbounded n).comp (continuous_applyMatrix_left x))
  have hnonempty : ∀ n : ℕ, (F n).Nonempty := by
    intro n
    obtain ⟨A, hA, he⟩ := tailEnvelope_succ_maximum M hM hneM hbounded n x
    refine ⟨A, hA, ?_⟩
    change stableGauge M x ≤ tailEnvelope M n (applyMatrix A x)
    rw [he]
    exact stableGauge_le_tailEnvelope M hM hneM hbounded (n + 1) x
  have hdecreasing : ∀ n : ℕ, F (n + 1) ⊆ F n := by
    intro n A hA
    exact ⟨hA.1, hA.2.trans (tailEnvelope_succ_le M hM hneM hbounded n (applyMatrix A x))⟩
  obtain ⟨A, hA⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F hdecreasing hnonempty (hM.inter_right (hclosed 0))
    (fun n => hM.isClosed.inter (hclosed n))
  have hAn : ∀ n : ℕ, A ∈ F n := Set.mem_iInter.mp hA
  have hAM : A ∈ M := (hAn 0).1
  refine ⟨A, hAM, le_antisymm (stableGauge_generator_le M hM hneM hbounded A hAM x) ?_⟩
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tailEnvelope_tendsto M hM hneM hbounded (applyMatrix A x)) (fun n => (hAn n).2)

#print axioms stable_gauge_max_recurrence
#assert_trust kernel stable_gauge_max_recurrence

end NLA.MF06

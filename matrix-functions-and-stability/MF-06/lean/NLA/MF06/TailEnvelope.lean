/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Each tail supremum ranges over every actual word of the specified length.
The norm domination makes these suprema finite. Mathlib's seminorm constructor
then supplies their exact homogeneity, including the zero scalar. Removing a
terminal segment of a chronological word proves the decreasing-tail property.
-/
import NLA.MF06.Envelope
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 Filter Topology

lemma tailValues_nonempty {d : ℕ} (M : Set (Square d)) (hneM : M.Nonempty)
    (n : ℕ) (x : EuclideanVector d) : (tailValues M n x).Nonempty := by
  obtain ⟨_, w, hw, hword, _⟩ := wordNorms_nonempty M hneM n
  exact ⟨_, w, hw, hword, rfl⟩

lemma tailValues_bddAbove {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x : EuclideanVector d) : BddAbove (tailValues M n x) := by
  refine ⟨boundedEnvelope M x, ?_⟩
  rintro r ⟨w, _, hw, rfl⟩
  exact boundedEnvelope_word_le M hM hneM hbounded w hw x

lemma word_le_tailEnvelope {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (w : List (Square d)) (hw : w.length = n) (hword : WordIn M w)
    (x : EuclideanVector d) :
    boundedEnvelope M (applyMatrix (matrixProduct w) x) ≤ tailEnvelope M n x := by
  exact le_csSup (tailValues_bddAbove M hM hneM hbounded n x) ⟨w, hw, hword, rfl⟩

lemma tailEnvelope_le_boundedEnvelope {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x : EuclideanVector d) :
    tailEnvelope M n x ≤ boundedEnvelope M x := by
  apply csSup_le (tailValues_nonempty M hneM n x)
  rintro r ⟨w, _, hw, rfl⟩
  exact boundedEnvelope_word_le M hM hneM hbounded w hw x

lemma tailEnvelope_nonneg {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x : EuclideanVector d) : 0 ≤ tailEnvelope M n x := by
  obtain ⟨_, w, hw, hword, rfl⟩ := tailValues_nonempty M hneM n x
  exact ((bounded_envelope_norm M hM hneM hbounded).1.1 _).trans
    (word_le_tailEnvelope M hM hneM hbounded n w hw hword x)

lemma tailEnvelope_zero_vector {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) : tailEnvelope M n (0 : EuclideanVector d) = 0 := by
  apply le_antisymm _ (tailEnvelope_nonneg M hM hneM hbounded n 0)
  calc
    tailEnvelope M n 0 ≤ boundedEnvelope M 0 :=
      tailEnvelope_le_boundedEnvelope M hM hneM hbounded n 0
    _ = 0 := complexNorm_zero (bounded_envelope_norm M hM hneM hbounded).1

lemma tailEnvelope_triangle {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x y : EuclideanVector d) :
    tailEnvelope M n (x + y) ≤ tailEnvelope M n x + tailEnvelope M n y := by
  apply csSup_le (tailValues_nonempty M hneM n (x + y))
  rintro r ⟨w, hw, hword, rfl⟩
  rw [applyMatrix_add_vector]
  exact ((bounded_envelope_norm M hM hneM hbounded).1.2.2.1 _ _).trans
    (add_le_add (word_le_tailEnvelope M hM hneM hbounded n w hw hword x)
      (word_le_tailEnvelope M hM hneM hbounded n w hw hword y))

lemma tailEnvelope_smul_le {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (c : ℂ) (x : EuclideanVector d) :
    tailEnvelope M n (c • x) ≤ ‖c‖ * tailEnvelope M n x := by
  apply csSup_le (tailValues_nonempty M hneM n (c • x))
  rintro r ⟨w, hw, hword, rfl⟩
  rw [applyMatrix_smul_vector, (bounded_envelope_norm M hM hneM hbounded).1.2.2.2]
  exact mul_le_mul_of_nonneg_left
    (word_le_tailEnvelope M hM hneM hbounded n w hw hword x) (norm_nonneg c)

/-- A bundled seminorm on the actual vectors, with the actual tail supremum as value. -/
def tailSeminorm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) : Seminorm ℂ (EuclideanVector d) :=
  Seminorm.ofSMulLE (tailEnvelope M n)
    (tailEnvelope_zero_vector M hM hneM hbounded n)
    (tailEnvelope_triangle M hM hneM hbounded n)
    (tailEnvelope_smul_le M hM hneM hbounded n)

@[simp] lemma tailSeminorm_apply {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x : EuclideanVector d) :
    tailSeminorm M hM hneM hbounded n x = tailEnvelope M n x := rfl

lemma tailEnvelope_smul {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (c : ℂ) (x : EuclideanVector d) :
    tailEnvelope M n (c • x) = ‖c‖ * tailEnvelope M n x :=
  map_smul_eq_mul (tailSeminorm M hM hneM hbounded n) c x

lemma tailEnvelope_continuous {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) : Continuous (tailEnvelope M n) := by
  change Continuous (tailSeminorm M hM hneM hbounded n : EuclideanVector d → ℝ)
  apply Seminorm.continuous_of_le (q := boundedEnvelopeSeminorm M hM hneM hbounded)
  · exact (bounded_envelope_norm M hM hneM hbounded).2.1
  · intro x
    exact tailEnvelope_le_boundedEnvelope M hM hneM hbounded n x

lemma tailEnvelope_succ_le {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (n : ℕ) (x : EuclideanVector d) :
    tailEnvelope M (n + 1) x ≤ tailEnvelope M n x := by
  apply csSup_le (tailValues_nonempty M hneM (n + 1) x)
  rintro r ⟨w, hw, hword, rfl⟩
  have hsplit : WordIn M (w.take n) ∧ WordIn M (w.drop n) := by
    apply (WordIn_append_iff M (w.take n) (w.drop n)).mp
    simpa only [List.take_append_drop] using hword
  have hlength : (w.take n).length = n := by
    simp only [List.length_take, hw]
    omega
  have hproduct : matrixProduct w = matrixProduct (w.drop n) * matrixProduct (w.take n) := by
    rw [← matrixProduct_append, List.take_append_drop]
  rw [hproduct, applyMatrix_mul]
  exact (boundedEnvelope_word_le M hM hneM hbounded (w.drop n) hsplit.2 _).trans
    (word_le_tailEnvelope M hM hneM hbounded n (w.take n) hlength hsplit.1 x)

lemma tailEnvelope_antitone {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) : Antitone (fun n : ℕ => tailEnvelope M n x) :=
  antitone_nat_of_succ_le (fun n => tailEnvelope_succ_le M hM hneM hbounded n x)

/-- The limit is exactly the frozen infimum definition, not a chosen limit witness. -/
lemma tailEnvelope_tendsto {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    Tendsto (fun n : ℕ => tailEnvelope M n x) atTop (𝓝 (stableGauge M x)) := by
  apply tendsto_atTop_ciInf (tailEnvelope_antitone M hM hneM hbounded x)
  refine ⟨0, ?_⟩
  rintro r ⟨n, rfl⟩
  exact tailEnvelope_nonneg M hM hneM hbounded n x

#print axioms tailEnvelope_tendsto
#assert_trust kernel tailEnvelope_tendsto
#print axioms tailEnvelope_continuous
#assert_trust kernel tailEnvelope_continuous

end NLA.MF06

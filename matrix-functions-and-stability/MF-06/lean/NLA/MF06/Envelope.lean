/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The reused MF07 word-envelope construction retains Matthew J. Colbrook's
mathematical attribution and the authorship recorded in those source files.

The product-bounded hypothesis bounds every actual word. Specializing the
published discounted envelope to rate one gives the required genuine norm;
the empty word provides definiteness even in dimension zero.
-/
import NLA.MF06.Definitions
import NLA.MF07.CompactGrowth
import NLA.MF07.NormGeometry
import NLA.MF07.Interspersed

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

/-- C05: the actual all-word supremum, without a positive-dimension assumption. -/
theorem bounded_envelope_norm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    IsComplexNorm (boundedEnvelope M) ∧ Continuous (boundedEnvelope M) ∧
    (∃ K : ℝ, 1 ≤ K ∧ ∀ x : EuclideanVector d,
      ‖x‖ ≤ boundedEnvelope M x ∧ boundedEnvelope M x ≤ K * ‖x‖) ∧
    (∀ A ∈ M, ∀ x : EuclideanVector d,
      boundedEnvelope M (applyMatrix A x) ≤ boundedEnvelope M x) := by
  obtain ⟨K, hK, hbound⟩ := hbounded
  have hword : ∀ w : List (Square d), WordIn M w →
      spectralNorm (matrixProduct (w.map (fun A => A))) ≤ K * (1 : ℝ) ^ w.length := by
    intro w hw
    simpa using (word_le_familyGrowth M hM w.length w rfl hw).trans (hbound w.length)
  have hv : IsComplexNorm (boundedEnvelope M) :=
    productEnvelope_isComplexNorm M (fun A => A) 1 K zero_lt_one hword
  have hb : ∀ x : EuclideanVector d,
      ‖x‖ ≤ boundedEnvelope M x ∧ boundedEnvelope M x ≤ K * ‖x‖ :=
    productEnvelope_bounds M (fun A => A) 1 K zero_lt_one hword
  refine ⟨hv, complexNorm_continuous hv K (zero_le_one.trans hK)
    (fun x => (hb x).2), ⟨K, hK, hb⟩, ?_⟩
  intro A hA x
  simpa only [boundedEnvelope, one_mul] using
    productEnvelope_generator M (fun A => A) 1 K zero_lt_one hword A hA x

/-- The same concrete norm as a Mathlib seminorm, for domination and limit APIs. -/
def boundedEnvelopeSeminorm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M) :
    Seminorm ℂ (EuclideanVector d) :=
  Seminorm.of (boundedEnvelope M)
    (bounded_envelope_norm M hM hneM hbounded).1.2.2.1
    (bounded_envelope_norm M hM hneM hbounded).1.2.2.2

@[simp] lemma boundedEnvelopeSeminorm_apply {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) :
    boundedEnvelopeSeminorm M hM hneM hbounded x = boundedEnvelope M x := rfl

/-- Reuse the existing chronological-word action lemma at rate one. -/
lemma boundedEnvelope_word_le {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (w : List (Square d)) (hw : WordIn M w) (x : EuclideanVector d) :
    boundedEnvelope M (applyMatrix (matrixProduct w) x) ≤ boundedEnvelope M x := by
  have hgen := (bounded_envelope_norm M hM hneM hbounded).2.2.2
  have hgen' : ∀ A ∈ M, ∀ x : EuclideanVector d,
      boundedEnvelope M (applyMatrix A x) ≤ (1 : ℝ) * boundedEnvelope M x := by
    simpa only [one_mul] using hgen
  simpa using norm_product_from_generator M (fun A => A) (boundedEnvelope M)
    1 zero_le_one hgen' w hw x

#print axioms bounded_envelope_norm
#assert_trust kernel bounded_envelope_norm
#print axioms boundedEnvelope_word_le
#assert_trust kernel boundedEnvelope_word_le

end NLA.MF06

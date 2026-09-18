/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The frozen restricted growth is a supremum of actual unit-vector actions,
with zero inserted. Its operator bound uses Mathlib's genuine domain-restricted
continuous linear maps. Invariance, rather than any perturbed-family flag
assumption, justifies submultiplicativity for the fixed reference subspace.
-/
import NLA.MF06.StableKernel
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma restrictedGrowth_values_bound {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (S : Submodule ℂ (EuclideanVector d)) (n : ℕ) :
    ∀ r ∈ insert 0 {r | ∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
      ∃ x : EuclideanVector d, x ∈ S ∧ ‖x‖ = 1 ∧
        r = ‖applyMatrix (matrixProduct w) x‖}, r ≤ familyGrowth M n := by
  rintro r (rfl | ⟨w, hw, hword, x, _, hnorm, rfl⟩)
  · exact familyGrowth_nonneg M hM hneM n
  · calc
      ‖applyMatrix (matrixProduct w) x‖ ≤ spectralNorm (matrixProduct w) * ‖x‖ :=
        norm_applyMatrix_le _ x
      _ = spectralNorm (matrixProduct w) := by rw [hnorm, mul_one]
      _ ≤ familyGrowth M n := word_le_familyGrowth M hM n w hw hword

lemma restrictedGrowth_nonneg {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (S : Submodule ℂ (EuclideanVector d)) (n : ℕ) : 0 ≤ restrictedGrowth M S n := by
  exact le_csSup ⟨familyGrowth M n, restrictedGrowth_values_bound M hM hneM S n⟩
    (Or.inl rfl)

lemma restrictedGrowth_le_familyGrowth {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (S : Submodule ℂ (EuclideanVector d)) (n : ℕ) :
    restrictedGrowth M S n ≤ familyGrowth M n := by
  exact csSup_le ⟨0, Or.inl rfl⟩ (restrictedGrowth_values_bound M hM hneM S n)

lemma word_le_restrictedGrowth {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (S : Submodule ℂ (EuclideanVector d)) (n : ℕ)
    (w : List (Square d)) (hw : w.length = n) (hword : WordIn M w)
    (x : EuclideanVector d) (hx : x ∈ S) (hnorm : ‖x‖ = 1) :
    ‖applyMatrix (matrixProduct w) x‖ ≤ restrictedGrowth M S n := by
  exact le_csSup ⟨familyGrowth M n, restrictedGrowth_values_bound M hM hneM S n⟩
    (Or.inr ⟨w, hw, hword, x, hx, hnorm, rfl⟩)

/-- The unit-vector supremum bounds the action on every vector of S. -/
lemma restricted_word_action_le {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (S : Submodule ℂ (EuclideanVector d)) (n : ℕ)
    (w : List (Square d)) (hw : w.length = n) (hword : WordIn M w)
    (x : EuclideanVector d) (hx : x ∈ S) :
    ‖applyMatrix (matrixProduct w) x‖ ≤ restrictedGrowth M S n * ‖x‖ := by
  let f : S →L[ℂ] EuclideanVector d :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (matrixProduct w)).domRestrict S
  have hf : ‖f‖ ≤ restrictedGrowth M S n := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (restrictedGrowth_nonneg M hM hneM S n)
    intro y hy
    exact word_le_restrictedGrowth M hM hneM S n w hw hword y y.property hy
  exact (f.le_opNorm ⟨x, hx⟩).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg x))

lemma restrictedGrowth_zero_le_one {d : ℕ} (M : Set (Square d))
    (S : Submodule ℂ (EuclideanVector d)) : restrictedGrowth M S 0 ≤ 1 := by
  unfold restrictedGrowth
  refine csSup_le (α := ℝ) ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨w, hw, _, x, _, hnorm, rfl⟩)
  · exact zero_le_one
  · have hw0 : w = [] := List.length_eq_zero_iff.mp hw
    simpa only [hw0, matrixProduct_nil, applyMatrix_one] using hnorm.le

lemma restrictedGrowth_submultiplicative {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty)
    (S : Submodule ℂ (EuclideanVector d)) (hS : FamilyInvariant M S) (m n : ℕ) :
    restrictedGrowth M S (m + n) ≤ restrictedGrowth M S m * restrictedGrowth M S n := by
  unfold restrictedGrowth
  refine csSup_le (α := ℝ) ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨w, hw, hword, x, hx, hnorm, rfl⟩)
  · exact mul_nonneg (restrictedGrowth_nonneg M hM hneM S m)
      (restrictedGrowth_nonneg M hM hneM S n)
  · have hu : (w.take m).length = m := by simp [List.length_take, hw]
    have hv : (w.drop m).length = n := by simp [List.length_drop, hw]
    have hsplit : WordIn M (w.take m) ∧ WordIn M (w.drop m) :=
      (WordIn_append_iff M _ _).mp (by simpa only [List.take_append_drop] using hword)
    have huS : applyMatrix (matrixProduct (w.take m)) x ∈ S :=
      familyInvariant_word M S hS (w.take m) hsplit.1 x hx
    have hleft := restricted_word_action_le M hM hneM S m (w.take m) hu hsplit.1 x hx
    have hright := restricted_word_action_le M hM hneM S n (w.drop m) hv hsplit.2
      (applyMatrix (matrixProduct (w.take m)) x) huS
    have hproduct : matrixProduct w = matrixProduct (w.drop m) * matrixProduct (w.take m) := by
      rw [← matrixProduct_append, List.take_append_drop]
    rw [hproduct, applyMatrix_mul]
    calc
      ‖applyMatrix (matrixProduct (w.drop m)) (applyMatrix (matrixProduct (w.take m)) x)‖ ≤
          restrictedGrowth M S n * ‖applyMatrix (matrixProduct (w.take m)) x‖ := hright
      _ ≤ restrictedGrowth M S n * (restrictedGrowth M S m * ‖x‖) :=
        mul_le_mul_of_nonneg_left hleft (restrictedGrowth_nonneg M hM hneM S n)
      _ = restrictedGrowth M S m * restrictedGrowth M S n := by rw [hnorm]; ring

lemma restrictedGrowth_top {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (n : ℕ) :
    restrictedGrowth M ⊤ n = familyGrowth M n := by
  refine le_antisymm (restrictedGrowth_le_familyGrowth M hM hneM ⊤ n) ?_
  obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained M hM hneM n
  rw [← he]
  apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (matrixProduct w)).opNorm_le_bound
    (restrictedGrowth_nonneg M hM hneM ⊤ n)
  intro x
  exact restricted_word_action_le M hM hneM ⊤ n w hw hword x (Submodule.mem_top)

#print axioms restrictedGrowth_submultiplicative
#assert_trust kernel restrictedGrowth_submultiplicative
#print axioms restrictedGrowth_top
#assert_trust kernel restrictedGrowth_top

end NLA.MF06

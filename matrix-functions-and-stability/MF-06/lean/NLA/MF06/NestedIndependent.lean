/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Nested independent spanning sets are constructed inside each actual subspace.
The extension choice is an ordinary vector-space basis extension, not a
common-invariant flag or block-decomposition assumption.
-/
import NLA.MF06.InvariantChain
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma exists_nested_independent_sets {d : ℕ}
    (F : ℕ → Submodule ℂ (EuclideanVector d)) (hF : Monotone F) (h0 : F 0 = ⊥) :
    ∃ S : ℕ → Set (EuclideanVector d), S 0 = ∅ ∧ Monotone S ∧
      ∀ n, LinearIndepOn ℂ id (S n) ∧ Submodule.span ℂ (S n) = F n := by
  classical
  let T (n : ℕ) := {s : Set (EuclideanVector d) //
    LinearIndepOn ℂ id s ∧ Submodule.span ℂ s = F n}
  let initial : T 0 := ⟨∅, linearIndepOn_empty ℂ id, by simpa only [Submodule.span_empty] using h0.symm⟩
  have subset_next (n : ℕ) (t : T n) : t.val ⊆ (F (n + 1) : Set (EuclideanVector d)) := by
    intro x hx
    apply hF (Nat.le_succ n)
    rw [← t.property.2]
    exact Submodule.subset_span hx
  let step (n : ℕ) (t : T n) : T (n + 1) :=
    ⟨t.property.1.extend (subset_next n t),
      t.property.1.linearIndepOn_extend (subset_next n t), by
        rw [t.property.1.span_extend_eq_span (subset_next n t), Submodule.span_eq]⟩
  let seq : (n : ℕ) → T n := fun n => Nat.rec initial step n
  refine ⟨fun n => (seq n).val, rfl, ?_, fun n => (seq n).property⟩
  apply monotone_nat_of_le_succ
  intro n
  exact (seq n).property.1.subset_extend (subset_next n (seq n))

#print axioms exists_nested_independent_sets
#assert_trust kernel exists_nested_independent_sets

end NLA.MF06

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

These frozen contracts use Mathlib's actual ordered, zero-extended singular values.
The all-rank SVD and the main matrix inequality remain separate proof obligations.
-/
import NLA.MI13.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

theorem singular_values_semantics {m n : ℕ} (A : Rect m n) :
    (∀ k, 0 ≤ singularValue A k) ∧ Antitone (singularValue A) ∧
    ∀ k, n ≤ k → singularValue A k = 0 := by
  refine ⟨(euclideanLin A).singularValues_nonneg,
    (euclideanLin A).singularValues_antitone, ?_⟩
  intro k hk
  exact (euclideanLin A).singularValues_of_finrank_le (by simpa using hk)

theorem singular_values_gram {m n : ℕ} (A : Rect m n) (i : Fin n) :
    singularValue A i.val ^ 2 = gramEigenvalue A i := by
  exact (euclideanLin A).sq_singularValues_fin
    (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)) i

#print axioms singular_values_semantics
#assert_trust kernel singular_values_semantics
#print axioms singular_values_gram
#assert_trust kernel singular_values_gram

end
end NLA.MI13

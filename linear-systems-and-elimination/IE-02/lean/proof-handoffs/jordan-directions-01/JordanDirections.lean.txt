/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 attribution is retained in
Definitions.lean and SourceCorrespondence.md. Reuses the proved Toeplitz algebra
homomorphism and Mathlib's algebra-hom power identity.
-/
import NLA.IE02.Toeplitz

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open Polynomial

theorem jordan_direction_toeplitz (n k : ℕ) (lam : ℂ) :
    IsToeplitz (1 : Square n) ∧ ∀ j, IsToeplitz (jordanDirections n k lam j) := by
  refine ⟨⟨1, (toeplitz_one n).symm⟩, ?_⟩
  intro j
  have hbase : (toeplitzAlgHom n) (C lam + X) = lowerJordan n lam := by
    exact (toeplitz_add n (C lam) X).trans (by rw [toeplitz_C]; rfl)
  refine ⟨(C lam + X) ^ (j.val + 1), ?_⟩
  -- The algebra hom has the frozen Toeplitz map as its underlying function.
  change lowerJordan n lam ^ (j.val + 1) = (toeplitzAlgHom n) ((C lam + X) ^ (j.val + 1))
  rw [map_pow, hbase]

#print axioms jordan_direction_toeplitz
#assert_trust kernel jordan_direction_toeplitz

end
end NLA.IE02

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; prior mathematical attribution retained.

Zero padding transports the proved square bound to the original rectangular
complex target with its actual Euclidean norms and ordered singular values.
-/
import NLA.MI13.MiddleBounds
import NLA.MI13.Padding

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

theorem canonical_rectangular_bound {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (A C : Rect m n) (B : Rect n m) :
    frobeniusNorm (A * B * C - C * B * A) ^ 2 ≤
      2 * spectralNorm B ^ 2 * (singularValue A 0 ^ 2 + singularValue A 1 ^ 2) *
        frobeniusNorm C ^ 2 := by
  have hr : 2 ≤ m + n := by omega
  have h := square_middle_bound hr (padUpper A) (padLower B) (padUpper C)
  rw [padding_product, (padding_norms (A * B * C - C * B * A) B).1,
    (padding_norms A B).2.2.2, (padding_singular_values A B 0).1,
    (padding_singular_values A B 1).1, (padding_norms C B).1] at h
  exact h

#print axioms canonical_rectangular_bound
#assert_trust kernel canonical_rectangular_bound

end
end NLA.MI13

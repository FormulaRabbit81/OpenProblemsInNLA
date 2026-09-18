/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 attribution is retained in
Definitions.lean and SourceCorrespondence.md. Mathlib supplies polynomial
root divisibility and exact product degrees. Algebraic division works for any
common root, so the frozen circle hypothesis hz is intentionally not needed here.
-/
import NLA.IE02.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open Polynomial

theorem common_circle_root_reduction {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (hq : ∀ j, DegreeLE (q j) m) (hne : ∃ j, q j ≠ 0)
    (z : ℂ) (hz : ‖z‖ = 1) (hroot : ∀ j, (q j).eval z = 0) :
    1 ≤ m ∧ ∃ r : Fin l → Poly,
      ∀ j, q j = (X - C z) * r j ∧ DegreeLE (r j) (m - 1) := by
  classical
  have hdiv : ∀ j, ∃ r : Poly, q j = (X - C z) * r := by
    intro j
    exact dvd_iff_isRoot.mpr (hroot j)
  choose r hr using hdiv
  have hdegree (j : Fin l) (hrne : r j ≠ 0) : 1 + (r j).natDegree ≤ m := by
    have hbound := natDegree_le_of_degree_le (hq j)
    rw [hr j, natDegree_mul (X_sub_C_ne_zero z) hrne, natDegree_X_sub_C] at hbound
    exact hbound
  have hm : 1 ≤ m := by
    obtain ⟨j, hj⟩ := hne
    have hrne : r j ≠ 0 := by
      intro hzero
      apply hj
      rw [hr j, hzero, mul_zero]
    have hbound := hdegree j hrne
    omega
  refine ⟨hm, r, fun j => ⟨hr j, ?_⟩⟩
  by_cases hzero : r j = 0
  · simp [DegreeLE, hzero]
  · apply degree_le_of_natDegree_le
    have hbound := hdegree j hzero
    omega

#print axioms common_circle_root_reduction
#assert_trust kernel common_circle_root_reduction

end
end NLA.IE02

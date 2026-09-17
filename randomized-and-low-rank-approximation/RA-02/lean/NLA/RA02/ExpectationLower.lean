/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.RA02.RetainedContribution
import NLA.RA02.FiniteExpectation

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

theorem expectation_lower_bound (r : ℕ) (hr : 1 ≤ r) :
    (2 : ℝ) ^ r * scaleParameter r ^ r / (1 + 1 / (r : ℝ)) ^ r ≤
      expectedTrace (arrowhead r) r := by
  classical
  have hcard := (retained_history_count r).2.1
  have hsum : (∑ _f ∈ retainedHistories r,
      scaleParameter r ^ r / (1 + 1 / (r : ℝ)) ^ r) ≤
      ∑ f ∈ retainedHistories r, pathContribution (arrowhead r) (List.ofFn f) := by
    apply Finset.sum_le_sum
    intro f hf
    obtain ⟨bits, hbits, rfl⟩ := Finset.mem_image.mp hf
    exact retained_contribution_bound r hr bits
  have hcount : (∑ _f ∈ retainedHistories r,
      scaleParameter r ^ r / (1 + 1 / (r : ℝ)) ^ r) =
      (2 : ℝ) ^ r * scaleParameter r ^ r / (1 + 1 / (r : ℝ)) ^ r := by
    simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [hcount] at hsum
  apply hsum.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro f _ _
  exact pathContribution_nonneg (arrowhead r)
    (arrowhead_positive_definite r hr).posSemidef (List.ofFn f)

#print axioms expectation_lower_bound
#assert_trust kernel expectation_lower_bound

end
end NLA.RA02

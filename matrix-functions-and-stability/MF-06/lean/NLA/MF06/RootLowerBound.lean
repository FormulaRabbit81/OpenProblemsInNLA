/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The transfer uses only integer powers on the unit interval. Fractional roots
and their numerical evaluation are unnecessary.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06

theorem root_lower_bound (k : ℕ) (hk : 1 ≤ k) (u z : ℝ)
    (hu : 0 ≤ u) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hz : z ≤ u ^ k) :
    z ≤ u := by
  rcases le_total 1 u with h | h
  · exact hz1.trans h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have hp : u ^ n ≤ 1 := pow_le_one₀ hu h
    apply hz.trans
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hu

#print axioms root_lower_bound
#assert_trust kernel root_lower_bound

end NLA.MF06

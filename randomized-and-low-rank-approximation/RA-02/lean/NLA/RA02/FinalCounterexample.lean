/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.RA02.ExponentialComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

theorem universal_counterexamples (C p : ℝ) (hC : 0 < C) (hp : 0 ≤ p) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ A : Square n, ∃ hA : A.PosDef, ∃ r : ℕ,
      1 ≤ r ∧ r ≤ n ∧ 0 < rankTail A hA.isHermitian r ∧
      C * Real.rpow (r : ℝ) p * rankTail A hA.isHermitian r < expectedTrace A r := by
  obtain ⟨r, hr, hpower⟩ := exponential_dominates_real_power C p hC hp
  have hA : (arrowhead r).PosDef := arrowhead_positive_definite r hr
  have htail := arrowhead_tail r hr hA.isHermitian
  refine ⟨r + 1, by omega, arrowhead r, hA, r, hr, by omega, htail.1, ?_⟩
  have hstrict := mul_lt_mul_of_pos_right hpower htail.1
  have hfactor := exponential_tail_factor r hr hA.isHermitian
  nlinarith only [hstrict, hfactor]

theorem no_polynomial_trace_factor : ¬ PolynomialTraceFactor := by
  intro h
  obtain ⟨C, hC, p, hp, hbound⟩ := h
  obtain ⟨n, hn, A, hA, r, hr, hrn, htail, hbad⟩ := universal_counterexamples C p hC hp
  have hle := hbound n hn A hA.posSemidef r hr hrn
  exact (not_lt_of_ge hle) hbad

#print axioms universal_counterexamples
#assert_trust kernel universal_counterexamples
#print axioms no_polynomial_trace_factor
#assert_trust kernel no_polynomial_trace_factor

end
end NLA.RA02

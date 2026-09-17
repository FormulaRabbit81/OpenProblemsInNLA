/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The explicit probe bounds the genuine positive spectral tail. The scalar
epsilon^r is an upper bound, never an alternate definition of that tail.
-/
import NLA.RA02.RayleighMinimum
import NLA.RA02.SpectralTail
import NLA.RA02.ProbeValues

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

theorem arrowhead_tail (r : ℕ) (hr : 1 ≤ r) (hA : (arrowhead r).IsHermitian) :
    0 < rankTail (arrowhead r) hA r ∧
    rankTail (arrowhead r) hA r ≤ scaleParameter r ^ r := by
  have hp : (arrowhead r).PosDef := arrowhead_positive_definite r hr
  have hx := rayleigh_probe_values r
  have hRay := least_eigenvalue_rayleigh r (arrowhead r) hA (rayleighProbe r) hx.1
  rw [hx.2.1] at hRay
  simp only [rankTail_last]
  refine ⟨orderedEigenvalues_pos (arrowhead r) hp hA (Fin.last r), hRay.trans ?_⟩
  exact div_le_self (pow_nonneg (scaleParameter_pos r).le r) hx.2.2.2

#print axioms arrowhead_tail
#assert_trust kernel arrowhead_tail

end
end NLA.RA02

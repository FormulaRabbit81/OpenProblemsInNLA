/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Definitions
import LeanCert.Tactic

namespace NLA.SP05

/-- Consumed by positivity of the full-dimensional skew witness's Frobenius square. -/
theorem skew_norm_positive_certificate : (0 : ℝ) < 2 := by
  interval_decide (trust := kernel)

#assert_trust kernel skew_norm_positive_certificate
#print axioms skew_norm_positive_certificate

end NLA.SP05

/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Definitions
import LeanCert.Tactic

namespace NLA.SP04

/-- Exact constants used in the radicand, root difference, product and endpoint bounds. -/
theorem scalar_numerical_bounds :
    (99 / 100 : ℝ) ^ 2 < 49 / 16 - 52 / 25 ∧
    (275 / 198 : ℝ) < 2 ∧
    (13 / 25 : ℝ) * (44 / 25) * (51 / 50) < 1 ∧
    (201 / 400 : ℝ) < 13 / 25 := by
  constructor
  · interval_decide (trust := kernel)
  constructor
  · interval_decide (trust := kernel)
  constructor <;> interval_decide (trust := kernel)

#assert_trust kernel scalar_numerical_bounds
#print axioms scalar_numerical_bounds

end NLA.SP04

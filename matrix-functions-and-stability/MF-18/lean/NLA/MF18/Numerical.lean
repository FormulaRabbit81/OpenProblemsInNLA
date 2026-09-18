/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Kernel certificate pattern follows NLA.MF05.Numerical by George Stepaniants
(that project's local-neighborhood argument is due to Matthew J. Colbrook).
Here the positive half is consumed by the positive-matrix averaging proof.
-/
import NLA.MF18.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF18

theorem certified_half : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  constructor <;> interval_decide (trust := kernel)

#print axioms certified_half
#assert_trust kernel certified_half

end NLA.MF18

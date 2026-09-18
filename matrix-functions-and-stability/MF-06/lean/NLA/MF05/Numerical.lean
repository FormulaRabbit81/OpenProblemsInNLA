/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original local-neighborhood argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, proof of Theorem 2.

The only new fixed numerical certificate is the half-radius. It will be
consumed by the common norm-ball bound and the final positive radius choice.
-/
import NLA.MF05.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05

theorem half_radius_certificate : 0 < localRadius ∧ localRadius < 1 := by
  constructor <;> dsimp only [localRadius] <;> interval_decide (trust := kernel)

#print axioms half_radius_certificate
#assert_trust kernel half_radius_certificate

end NLA.MF05

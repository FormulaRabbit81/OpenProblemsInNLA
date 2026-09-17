/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; prior mathematical attribution retained.

Scalar normalization uses the actual Euclidean operator norm.
-/
import NLA.MI13.OperatorNorm

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

theorem euclideanCLM_smul {m n : ℕ} (z : ℂ) (A : Rect m n) :
    euclideanCLM (z • A) = z • euclideanCLM A := by
  simp only [euclideanCLM, euclideanLin, map_smul]

theorem spectralNorm_smul {m n : ℕ} (z : ℂ) (A : Rect m n) :
    spectralNorm (z • A) = ‖z‖ * spectralNorm A := by
  simp only [spectralNorm, euclideanCLM_smul, norm_smul]

theorem spectralNorm_nonneg {m n : ℕ} (A : Rect m n) : 0 ≤ spectralNorm A :=
  norm_nonneg (euclideanCLM A)

#print axioms spectralNorm_smul
#assert_trust kernel spectralNorm_smul

end
end NLA.MI13

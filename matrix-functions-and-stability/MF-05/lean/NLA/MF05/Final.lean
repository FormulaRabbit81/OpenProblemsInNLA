/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Theorem 2.

The radius and Holder constant are fixed before either family varies. The
operator Hausdorff metric is replaced by the original max-of-sup-inf formula
using the proved compact-family identity. This is the full canonical target.
-/
import NLA.MF05.UniformHolder
import NLA.MF05.LocalBall

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

theorem canonical_local_holder {d : ℕ} (hd : 1 ≤ d) (M0 : Set (Square d))
    (hM0 : IsCompact M0) (hne0 : M0.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ M N : Set (Square d),
        IsCompact M → M.Nonempty → IsCompact N → N.Nonempty →
        canonicalHausdorff M M0 < r → canonicalHausdorff N M0 < r →
        |jointSpectralRadius M - jointSpectralRadius N| ≤
          C * Real.rpow (canonicalHausdorff M N) (1 / (d : ℝ)) := by
  have hball := local_common_norm_ball hd M0 hM0 hne0
  have hc := holderConstant_pos hd (localNormBound M0) hball.1
  refine ⟨localRadius, half_radius_certificate.1,
    holderConstant d (localNormBound M0), hc, ?_⟩
  intro M N hM hneM hN hneN hnearM hnearN
  have hMb : InNormBall M (localNormBound M0) := hball.2 M hM hneM (by
    rw [spectralHausdorff_eq_canonical M M0 hM hneM hM0 hne0]
    exact hnearM)
  have hNb : InNormBall N (localNormBound M0) := hball.2 N hN hneN (by
    rw [spectralHausdorff_eq_canonical N M0 hN hneN hM0 hne0]
    exact hnearN)
  simpa only [spectralHausdorff_eq_canonical M N hM hneM hN hneN] using
    (uniform_holder_estimate hd M N hM hneM hN hneN
      (localNormBound M0) hball.1 hMb hNb).2

#print axioms canonical_local_holder
#assert_trust kernel canonical_local_holder

end NLA.MF05

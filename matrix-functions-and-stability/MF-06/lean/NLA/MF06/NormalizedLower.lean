/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The fully proved critical-degree theorem discharges the exterior hypotheses
of the lower-transfer lemma. The reference and perturbation remain arbitrary
nonempty compact families; the reference need not be product bounded.
-/
import NLA.MF06.CriticalCompound
import NLA.MF06.CompoundLowerTransfer

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

theorem normalized_pointwise_lower_lipschitz {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hradius : jointSpectralRadius M = 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        1 - C * canonicalHausdorff M N ≤ jointSpectralRadius N := by
  obtain ⟨k, hk0, hkd, hcritical, hbounded, _⟩ :=
    critical_compound_product_bounded hd M hM hneM hradius
  exact lower_lipschitz_of_critical_compound hd M hM hneM k hk0 hkd hcritical hbounded

#print axioms normalized_pointwise_lower_lipschitz
#assert_trust kernel normalized_pointwise_lower_lipschitz

end NLA.MF06

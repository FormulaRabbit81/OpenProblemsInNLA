/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The strict-radius case uses the proved all-word exponential envelope with
base one. Only the radius-one case invokes irreducible boundedness.
-/
import NLA.MF06.IrreducibleBounded
import NLA.MF05.GeneralEnvelope

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma irreducible_radius_le_one_product_bounded {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hirr : FamilyIrreducible M) (hradius : jointSpectralRadius M ≤ 1) :
    IsProductBounded M := by
  rcases lt_or_eq_of_le hradius with hlt | heq
  · obtain ⟨_, K, hK, hbound⟩ := general_exponential_envelope hd M hM hneM 1 hlt
    exact ⟨K, hK, fun n => by simpa only [one_pow, mul_one] using hbound n⟩
  · exact irreducible_radius_one_product_bounded hd M hM hneM hirr heq

#print axioms irreducible_radius_le_one_product_bounded
#assert_trust kernel irreducible_radius_le_one_product_bounded

end NLA.MF06

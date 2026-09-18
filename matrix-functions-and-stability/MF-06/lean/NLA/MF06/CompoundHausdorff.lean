/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The proved symbolic minor Lipschitz bound applies to both compact families
in the given norm ball, and actual nearest-generator matching transfers it.
-/
import NLA.MF06.HausdorffImages
import NLA.MF06.CompoundLipschitz
import NLA.MF06.AllocationProducts

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

theorem compound_hausdorff_bound {d : ℕ} (k : ℕ) (hk0 : 1 ≤ k) (hkd : k ≤ d)
    (M N : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hN : IsCompact N) (hneN : N.Nonempty) (L : ℝ) (hL : 0 < L)
    (hML : InNormBall M L) (hNL : InNormBall N L) :
    canonicalHausdorff (compoundFamily k M) (compoundFamily k N) ≤
      compoundLipschitzConstant d k L * canonicalHausdorff M N := by
  have hball (A : Square d) (hA : A ∈ M ∪ N) : spectralNorm A ≤ L :=
    hA.elim (hML A) (hNL A)
  obtain ⟨A, hA⟩ := hneM
  have hC := (compound_local_lipschitz k hk0 hkd L hL A A (hML A hA) (hML A hA)).1
  exact canonicalHausdorff_image_le M N hM ⟨A, hA⟩ hN hneN (compoundMatrix k)
    (continuous_compoundMatrix k) _ hC.le (fun A hA B hB =>
      (compound_local_lipschitz k hk0 hkd L hL A B (hball A hA) (hball B hB)).2)

#print axioms compound_hausdorff_bound
#assert_trust kernel compound_hausdorff_bound

end NLA.MF06

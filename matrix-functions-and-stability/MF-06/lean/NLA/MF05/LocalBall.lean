/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Theorem 2.

The kernel-certified half-radius puts every nearby compact family in one
explicit spectral-norm ball. Actual nearest generators supply the triangle
inequality; no finite-family approximation or radius continuity is used.
-/
import NLA.MF05.Hausdorff
import NLA.MF05.Numerical
import NLA.MF07.CompactGrowth

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

theorem local_common_norm_ball {d : ℕ} (hd : 1 ≤ d) (M0 : Set (Square d))
    (hM0 : IsCompact M0) (hne0 : M0.Nonempty) :
    0 < localNormBound M0 ∧
    ∀ M : Set (Square d), IsCompact M → M.Nonempty →
      spectralHausdorff M M0 < localRadius → InNormBall M (localNormBound M0) := by
  have hhalf := half_radius_certificate
  have hmax := family_norm_maximum hd M0 hM0 hne0
  have hone : (0 : ℝ) < 1 := hhalf.1.trans hhalf.2
  refine ⟨add_pos_of_nonneg_of_pos hmax.1 hone, ?_⟩
  intro M hM hne hnear A hA
  obtain ⟨B, hB, heq⟩ := spectral_nearest_generator A M0 hM0 hne0
  have hdist : spectralNorm (A - B) ≤ spectralHausdorff M M0 :=
    heq ▸ pointFamilyDistance_le_hausdorff M M0 hM hne hM0 hne0 A hA
  calc
    spectralNorm A = spectralNorm ((A - B) + B) :=
      congrArg spectralNorm (sub_add_cancel A B).symm
    _ ≤ spectralNorm (A - B) + spectralNorm B := spectralNorm_add_le _ _
    _ ≤ spectralHausdorff M M0 + familyNorm M0 := add_le_add hdist (hmax.2.2 B hB)
    _ ≤ 1 + familyNorm M0 := add_le_add (hnear.trans hhalf.2).le le_rfl
    _ = localNormBound M0 := add_comm _ _

#print axioms local_common_norm_ball
#assert_trust kernel local_common_norm_ball

end NLA.MF05

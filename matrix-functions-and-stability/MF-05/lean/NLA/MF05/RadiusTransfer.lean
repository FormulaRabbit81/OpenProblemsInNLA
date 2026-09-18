/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, uniform_growth_and_holder.tex, Theorem 2.

An attained nearest generator transfers the constructed comparison norm to
the second family. Bounds on every actual word imply a bound on its actual
joint spectral radius. No norm ball on the second family is assumed.
-/
import NLA.MF05.ComparisonNorm
import NLA.MF05.Hausdorff

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF05
open NLA.MF07

theorem hausdorff_radius_transfer {d : ℕ} (hd : 1 ≤ d) (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L s : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hs : 1 ≤ s) :
    jointSpectralRadius N ≤
      comparisonRate d M L s + comparisonFactor d s * spectralHausdorff M N := by
  let v := comparisonNorm d M L s
  let K := comparisonFactor d s
  let u := comparisonRate d M L s
  let delta := spectralHausdorff M N
  obtain ⟨hu, hv, hbounds, haction⟩ := controlled_comparison_norm hd M hM hneM L s hL hML hs
  have hK : 1 ≤ K := comparisonFactor_ge_one d hd s hs
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hd0 : 0 ≤ delta := Metric.hausdorffDist_nonneg
  have hb : 0 < u + K * delta := add_pos_of_pos_of_nonneg hu (mul_nonneg hK0 hd0)
  have hletter (B : Square d) (hB : B ∈ N) (x : EuclideanVector d) :
      v (applyMatrix B x) ≤ (u + K * delta) * v x := by
    obtain ⟨A, hA, heq⟩ := spectral_nearest_generator B M hM hneM
    have hdist : spectralNorm (B - A) ≤ delta := by
      calc
        spectralNorm (B - A) ≤ spectralHausdorff N M :=
          heq ▸ pointFamilyDistance_le_hausdorff N M hN hneN hM hneM B hB
        _ = delta := Metric.hausdorffDist_comm
    have herror : v (applyMatrix (B - A) x) ≤ K * delta * v x := by
      calc
        v (applyMatrix (B - A) x) ≤ K * ‖applyMatrix (B - A) x‖ := (hbounds _).2
        _ ≤ K * (spectralNorm (B - A) * ‖x‖) :=
          mul_le_mul_of_nonneg_left (norm_applyMatrix_le _ _) hK0
        _ ≤ K * (delta * ‖x‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdist (norm_nonneg x)) hK0
        _ ≤ K * (delta * v x) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbounds x).1 hd0) hK0
        _ = K * delta * v x := (mul_assoc _ _ _).symm
    have hsplit : applyMatrix B x = applyMatrix A x + applyMatrix (B - A) x := by
      rw [← applyMatrix_add]
      congr 1
      abel
    calc
      v (applyMatrix B x) = v (applyMatrix A x + applyMatrix (B - A) x) := congrArg v hsplit
      _ ≤ v (applyMatrix A x) + v (applyMatrix (B - A) x) := hv.2.2.1 _ _
      _ ≤ u * v x + K * delta * v x := add_le_add (haction A hA x) herror
      _ = (u + K * delta) * v x := (add_mul _ _ _).symm
  apply exponential_bound_controls_radius hd N hN hneN K (u + K * delta) hK hb
  intro n
  obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained N hN hneN n
  rw [← he, ← hw]
  -- Reuse the published all-word operator bound with the identity generator map.
  simpa only [List.map_id_fun', id_eq] using
    spectralNorm_product_of_norm N (fun A => A) v K (u + K * delta) hK0 hb.le
      hbounds hletter w hword

#print axioms hausdorff_radius_transfer
#assert_trust kernel hausdorff_radius_transfer

end NLA.MF05

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
Reused MF05/MF07 mathematics retain the attribution in their pinned sources.

The complete product-bounded reference case. The neighborhood and Lipschitz
constant are fixed before the arbitrary compact perturbing family is supplied.
Actual cone trajectories provide legal words at every length, and the actual
joint spectral radius follows from their exponential lower growth. This is
C10 only; the later exterior-power reduction for arbitrary references remains.
-/
import NLA.MF06.PerturbationCone
import NLA.MF06.ConeWords

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

/-- C10: the complete product-bounded, radius-one reference-family lemma. -/
theorem product_bounded_lower_lipschitz {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hneM : M.Nonempty)
    (hbounded : IsProductBounded M) (hradius : jointSpectralRadius M = 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (Square d), IsCompact N → N.Nonempty →
        canonicalHausdorff M N < r →
        1 - C * canonicalHausdorff M N ≤ jointSpectralRadius N := by
  obtain ⟨a, q, K, Ca, Cb, c, hq0, hq1, hK, hCa, hCb, hc, hbound, hreference,
    x₀, hstarta, hstartb⟩ := reference_cone_data hd M hM hneM hbounded hradius
  obtain ⟨hH, hL, _hrest⟩ :=
    cone_numerical_bound q K 0 hq0 hq1 hK le_rfl (by positivity)
  have hH0 : 0 ≤ coneHeight q K := zero_le_one.trans hH
  have hLpos : 0 < coneLoss q K := by linarith
  let c₀ : ℝ := (Ca + Cb) * c
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact mul_pos (by linarith) hc
  let r : ℝ := (1 / coneLoss q K ^ 2) / c₀
  let C : ℝ := coneLoss q K * c₀
  have hr : 0 < r := div_pos (one_div_pos.mpr (pow_pos hLpos 2)) hc₀
  have hC : 0 < C := mul_pos hLpos hc₀
  refine ⟨r, hr, C, hC, ?_⟩
  intro N hN hneN hnear
  let δ := canonicalHausdorff M N
  have hδ : 0 ≤ δ := by
    change 0 ≤ canonicalHausdorff M N
    rw [← spectralHausdorff_eq_canonical M N hM hneM hN hneN]
    exact Metric.hausdorffDist_nonneg
  have hsmall : c₀ * δ ≤ 1 / coneLoss q K ^ 2 := by
    have hproduct : δ * c₀ < 1 / coneLoss q K ^ 2 := (lt_div_iff₀ hc₀).mp hnear
    simpa only [mul_comm] using hproduct.le
  let γ : ℝ := 1 - coneLoss q K * (c₀ * δ)
  have hγ : 0 < γ := (cone_numerical_bound q K (c₀ * δ) hq0 hq1 hK
    (mul_nonneg hc₀.le hδ) hsmall).2.2.2.2.2
  have hstep : ∀ x : EuclideanVector d,
      a x ≤ coneHeight q K * stableGauge M x → 0 < stableGauge M x →
      ∃ B ∈ N,
        a (applyMatrix B x) ≤ coneHeight q K * stableGauge M (applyMatrix B x) ∧
        γ * stableGauge M x ≤ stableGauge M (applyMatrix B x) ∧
        0 < stableGauge M (applyMatrix B x) :=
    matched_cone_step M hM hneM hbounded a q K Ca Cb c hq0 hq1 hK hCa hCb hc
      hbound hreference N hN hneN hsmall
  have hstart : a x₀ ≤ coneHeight q K * stableGauge M x₀ := by
    rw [hstarta, hstartb, mul_one]
    exact hH0
  have hwords := cone_trajectory_words N a (stableGauge M) (coneHeight q K) γ hγ.le
    hstep x₀ hstart hstartb
  have hCb0 : 0 ≤ Cb := zero_le_one.trans hCb
  have hD : 1 ≤ Cb * ‖x₀‖ := by simpa only [hstartb] using (hbound x₀).2.1
  have hlower : ∀ n : ℕ, γ ^ n ≤ (Cb * ‖x₀‖) * familyGrowth N n := by
    intro n
    obtain ⟨w, hw, hword, _hcone, hgrowth, _hpositive⟩ := hwords n
    calc
      γ ^ n ≤ stableGauge M (applyMatrix (matrixProduct w) x₀) := hgrowth
      _ ≤ Cb * ‖applyMatrix (matrixProduct w) x₀‖ := (hbound _).2.1
      _ ≤ Cb * (spectralNorm (matrixProduct w) * ‖x₀‖) :=
        mul_le_mul_of_nonneg_left (norm_applyMatrix_le _ _) hCb0
      _ ≤ Cb * (familyGrowth N n * ‖x₀‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (word_le_familyGrowth N hN n w hw hword) (norm_nonneg x₀)) hCb0
      _ = (Cb * ‖x₀‖) * familyGrowth N n := by ring
  have hradiusN := radius_ge_of_exponential_lower_bound hd N hN hneN (Cb * ‖x₀‖) γ hD hγ hlower
  change 1 - C * δ ≤ jointSpectralRadius N
  calc
    1 - C * δ = γ := by dsimp only [C, γ]; ring
    _ ≤ jointSpectralRadius N := hradiusN

#print axioms product_bounded_lower_lipschitz
#assert_trust kernel product_bounded_lower_lipschitz

end NLA.MF06

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.
The imported spectral Hausdorff semantics retain MF05's Colbrook attribution.

One actual reference generator attains the quotient max recurrence, and an
actual nearest generator is chosen from the arbitrary compact perturbing
family. Both component errors are bounded in the original operator norm.
The certified symbolic cone inequality preserves the cone and positive growth;
no invariance of the stable subspace is assumed for the perturbing generator.
-/
import NLA.MF06.ReferenceCone
import NLA.MF06.ConeNumerical
import NLA.MF05.Hausdorff
import NLA.MF07.QuantitativeComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07 NLA.MF05

lemma seminorm_matrix_error {d : ℕ} (p : Seminorm ℂ (EuclideanVector d))
    (C : ℝ) (hC : 0 ≤ C) (hp : ∀ y : EuclideanVector d, p y ≤ C * ‖y‖)
    (δ : ℝ) (A B : Square d) (hdist : spectralNorm (A - B) ≤ δ) (x : EuclideanVector d) :
    ‖p (applyMatrix A x) - p (applyMatrix B x)‖ ≤ C * δ * ‖x‖ := by
  calc
    ‖p (applyMatrix A x) - p (applyMatrix B x)‖ ≤
        p (applyMatrix A x - applyMatrix B x) := p.norm_sub_map_le_sub _ _
    _ = p (applyMatrix (A - B) x) := congrArg p (applyMatrix_sub A B x).symm
    _ ≤ C * ‖applyMatrix (A - B) x‖ := hp _
    _ ≤ C * (spectralNorm (A - B) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_applyMatrix_le _ _) hC
    _ ≤ C * (δ * ‖x‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hdist (norm_nonneg x)) hC
    _ = C * δ * ‖x‖ := (mul_assoc _ _ _).symm

lemma matched_cone_step {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (a : Seminorm ℂ (EuclideanVector d)) (q K Ca Cb c : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hK : 0 ≤ K) (hCa : 1 ≤ Ca) (hCb : 1 ≤ Cb)
    (hc : 0 < c)
    (hbound : ∀ y : EuclideanVector d,
      a y ≤ Ca * ‖y‖ ∧ stableGauge M y ≤ Cb * ‖y‖ ∧
        ‖y‖ ≤ c * (a y + stableGauge M y))
    (hreference : ∀ A ∈ M, ∀ y : EuclideanVector d,
      a (applyMatrix A y) ≤ q * a y + K * stableGauge M y)
    (N : Set (Square d)) (hN : IsCompact N) (hneN : N.Nonempty)
    (hsmall : ((Ca + Cb) * c) * canonicalHausdorff M N ≤ 1 / coneLoss q K ^ 2)
    (x : EuclideanVector d) (hcone : a x ≤ coneHeight q K * stableGauge M x)
    (hx : 0 < stableGauge M x) :
    ∃ B ∈ N,
      a (applyMatrix B x) ≤ coneHeight q K * stableGauge M (applyMatrix B x) ∧
      (1 - coneLoss q K * (((Ca + Cb) * c) * canonicalHausdorff M N)) * stableGauge M x ≤
        stableGauge M (applyMatrix B x) ∧
      0 < stableGauge M (applyMatrix B x) := by
  let δ := canonicalHausdorff M N
  let U := Ca + Cb
  let t := (U * c) * δ
  have hδ : 0 ≤ δ := by
    change 0 ≤ canonicalHausdorff M N
    rw [← spectralHausdorff_eq_canonical M N hM hneM hN hneN]
    exact Metric.hausdorffDist_nonneg
  have hU : 0 ≤ U := by dsimp only [U]; linarith
  have ht : 0 ≤ t := mul_nonneg (mul_nonneg hU hc.le) hδ
  obtain ⟨hH, _hL, hidentity, hconeScalar, _hhalf, hpositive⟩ :=
    cone_numerical_bound q K t hq0 hq1 hK ht hsmall
  have hH0 : 0 ≤ coneHeight q K := zero_le_one.trans hH
  obtain ⟨A, hA, hmax⟩ := (stable_gauge_max_recurrence M hM hneM hbounded x).2
  obtain ⟨B, hB, hnearest⟩ := spectral_nearest_generator A N hN hneN
  have hdist : spectralNorm (A - B) ≤ δ := by
    change spectralNorm (A - B) ≤ canonicalHausdorff M N
    rw [← hnearest, ← spectralHausdorff_eq_canonical M N hM hneM hN hneN]
    exact pointFamilyDistance_le_hausdorff M N hM hneM hN hneN A hA
  have herror (v : Seminorm ℂ (EuclideanVector d))
      (hv : ∀ y : EuclideanVector d, v y ≤ U * ‖y‖) :
      ‖v (applyMatrix A x) - v (applyMatrix B x)‖ ≤ t * (a x + stableGauge M x) := by
    calc
      ‖v (applyMatrix A x) - v (applyMatrix B x)‖ ≤ U * δ * ‖x‖ :=
        seminorm_matrix_error v U hU hv δ A B hdist x
      _ ≤ (U * δ) * (c * (a x + stableGauge M x)) :=
        mul_le_mul_of_nonneg_left (hbound x).2.2 (mul_nonneg hU hδ)
      _ = t * (a x + stableGauge M x) := by dsimp only [t]; ring
  have hCaU : Ca ≤ U := by dsimp only [U]; linarith
  have hCbU : Cb ≤ U := by dsimp only [U]; linarith
  have haerror := herror a (fun y => (hbound y).1.trans
    (mul_le_mul_of_nonneg_right hCaU (norm_nonneg y)))
  have hberror := herror (stableSeminorm M hM hneM hbounded)
    (fun y => (hbound y).2.1.trans (mul_le_mul_of_nonneg_right hCbU (norm_nonneg y)))
  have haabs : |a (applyMatrix A x) - a (applyMatrix B x)| ≤ t * (a x + stableGauge M x) := by
    simpa only [Real.norm_eq_abs] using haerror
  have hbabs : |stableGauge M (applyMatrix A x) - stableGauge M (applyMatrix B x)| ≤
      t * (a x + stableGauge M x) := by
    simpa only [Real.norm_eq_abs, stableSeminorm_apply] using hberror
  have hsum : a x + stableGauge M x ≤ coneLoss q K * stableGauge M x := by
    dsimp only [coneLoss]
    nlinarith
  have hsmallerror : t * (a x + stableGauge M x) ≤
      (coneLoss q K * t) * stableGauge M x := by
    calc
      t * (a x + stableGauge M x) ≤ t * (coneLoss q K * stableGauge M x) :=
        mul_le_mul_of_nonneg_left hsum ht
      _ = (coneLoss q K * t) * stableGauge M x := by ring
  have haletter : a (applyMatrix B x) ≤ a (applyMatrix A x) +
      (coneLoss q K * t) * stableGauge M x := by
    have hdiff := (abs_sub_le_iff.mp haabs).2
    linarith
  have hlower : (1 - coneLoss q K * t) * stableGauge M x ≤ stableGauge M (applyMatrix B x) := by
    have hdiff := (abs_sub_le_iff.mp hbabs).1
    rw [hmax] at hdiff
    nlinarith
  have hupper : a (applyMatrix B x) ≤
      (coneHeight q K - 1 + coneLoss q K * t) * stableGauge M x := by
    calc
      a (applyMatrix B x) ≤ (q * a x + K * stableGauge M x) +
          (coneLoss q K * t) * stableGauge M x :=
        haletter.trans (add_le_add (hreference A hA x) le_rfl)
      _ ≤ (q * (coneHeight q K * stableGauge M x) + K * stableGauge M x) +
          (coneLoss q K * t) * stableGauge M x :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hcone hq0) le_rfl) le_rfl
      _ = (q * coneHeight q K + K + coneLoss q K * t) * stableGauge M x := by ring
      _ = (coneHeight q K - 1 + coneLoss q K * t) * stableGauge M x := by rw [hidentity]
  refine ⟨B, hB, ?_, hlower, (mul_pos hpositive hx).trans_le hlower⟩
  calc
    a (applyMatrix B x) ≤ (coneHeight q K - 1 + coneLoss q K * t) * stableGauge M x := hupper
    _ ≤ coneHeight q K * ((1 - coneLoss q K * t) * stableGauge M x) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hconeScalar hx.le
    _ ≤ coneHeight q K * stableGauge M (applyMatrix B x) :=
      mul_le_mul_of_nonneg_left hlower hH0

#print axioms matched_cone_step
#assert_trust kernel matched_cone_step

end NLA.MF06

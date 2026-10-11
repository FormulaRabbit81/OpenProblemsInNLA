import NLA.RowDeletion.GaussianTrimming
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.IntermediateValue

/-! # Existence and uniqueness of the Gaussian cutoff

The cutoff is obtained directly from the continuous, strictly increasing mass
of symmetric intervals. This avoids introducing an inverse CDF or a choice of
quantile, and proves that the common target's cutoff hypothesis is nonvacuous.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace NLA.RowDeletion

lemma gaussian_interval_mass {a : ℝ} (ha : 0 ≤ a) :
    (gaussianReal 0 1).real (Set.Icc (-a) a) =
      ∫ x in (-a)..a, gaussianPDFReal 0 1 x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (integral_nonneg (fun x ↦ gaussianPDFReal_nonneg 0 1 x)),
    intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    integral_Icc_eq_integral_Ioc]

lemma continuous_gaussian_interval_integral :
    Continuous (fun a : ℝ ↦ ∫ x in (-a)..a, gaussianPDFReal 0 1 x) := by
  have h := (integrable_gaussianPDFReal 0 1).continuous_primitive 0
  have he : (fun a : ℝ ↦ ∫ x in (-a)..a, gaussianPDFReal 0 1 x) =
      fun a ↦ (∫ x in (0 : ℝ)..a, gaussianPDFReal 0 1 x) -
        ∫ x in (0 : ℝ)..(-a), gaussianPDFReal 0 1 x := by
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      (integrable_gaussianPDFReal 0 1).intervalIntegrable
      (integrable_gaussianPDFReal 0 1).intervalIntegrable).symm
  rw [he]
  exact h.sub (h.comp continuous_neg)

lemma strictMonoOn_gaussian_interval_integral :
    StrictMonoOn (fun a : ℝ ↦ ∫ x in (-a)..a, gaussianPDFReal 0 1 x) (Set.Ici 0) := by
  intro a ha b hb hab
  have hf : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal
    fun_prop
  have hp : 0 < ∫ x in a..b, gaussianPDFReal 0 1 x :=
    intervalIntegral.integral_pos hab hf.continuousOn
      (fun x _ ↦ gaussianPDFReal_nonneg 0 1 x)
      ⟨a, ⟨le_rfl, hab.le⟩, gaussianPDFReal_pos 0 1 a one_ne_zero⟩
  have hn : 0 ≤ ∫ x in (-b)..(-a), gaussianPDFReal 0 1 x :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun x _ ↦ gaussianPDFReal_nonneg 0 1 x)
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    ((integrable_gaussianPDFReal 0 1).intervalIntegrable (a := -b) (b := -a))
    ((integrable_gaussianPDFReal 0 1).intervalIntegrable (a := -a) (b := a))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    ((integrable_gaussianPDFReal 0 1).intervalIntegrable (a := -b) (b := a))
    ((integrable_gaussianPDFReal 0 1).intervalIntegrable (a := a) (b := b))
  linarith

lemma tendsto_gaussian_interval_integral :
    Tendsto (fun a : ℝ ↦ ∫ x in (-a)..a, gaussianPDFReal 0 1 x) atTop (𝓝 1) := by
  simpa only [integral_gaussianPDFReal_eq_one 0 one_ne_zero, id_eq] using
    intervalIntegral_tendsto_integral (integrable_gaussianPDFReal 0 1)
      tendsto_neg_atTop_atBot tendsto_id

theorem gaussianCutoff_existsUnique {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃! a : ℝ, GaussianCutoff θ a := by
  obtain ⟨b, hb, hmass⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (tendsto_gaussian_interval_integral.eventually (lt_mem_nhds hθ₁))).exists
  obtain ⟨a, ha, he⟩ := intermediate_value_Icc hb.le
    continuous_gaussian_interval_integral.continuousOn
    (show θ ∈ Set.Icc (∫ x in (-(0 : ℝ))..0, gaussianPDFReal 0 1 x)
      (∫ x in (-b)..b, gaussianPDFReal 0 1 x) by simpa using And.intro hθ₀.le hmass.le)
  have ha₀ : 0 < a := by
    have hne : a ≠ 0 := by
      intro hz
      subst a
      simp at he
      linarith
    exact lt_of_le_of_ne ha.1 (Ne.symm hne)
  refine ⟨a, ⟨ha₀, (gaussian_interval_mass ha₀.le).trans he⟩, ?_⟩
  intro b hb
  apply strictMonoOn_gaussian_interval_integral.injOn hb.1.le ha₀.le
  change (∫ x in (-b)..b, gaussianPDFReal 0 1 x) =
    ∫ x in (-a)..a, gaussianPDFReal 0 1 x
  rw [← gaussian_interval_mass hb.1.le, ← gaussian_interval_mass ha₀.le, hb.2,
    (gaussian_interval_mass ha₀.le).trans he]

end NLA.RowDeletion

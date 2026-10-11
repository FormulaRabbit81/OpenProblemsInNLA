import NLA.RowDeletion.Definitions
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-! # The specified spherical row law is a probability law with unit rows -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLA.RowDeletion

theorem isProbabilityMeasure_sphericalLaw {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (sphericalLaw n) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let σ := (volume : Measure (Vector n)).toSphere
  have hσ : σ Set.univ ≠ 0 :=
    fun h ↦ Measure.toSphere_ne_zero (volume : Measure (Vector n)) (Measure.measure_univ_eq_zero.mp h)
  refine ⟨?_⟩
  change (σ Set.univ)⁻¹ *
    σ.map (fun u : Metric.sphere (0 : Vector n) 1 ↦ (u : Vector n)) Set.univ = 1
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]
  exact ENNReal.inv_mul_cancel hσ (measure_ne_top σ Set.univ)

theorem ae_sphericalLaw_norm (n : ℕ) : ∀ᵐ x ∂sphericalLaw n, ‖x‖ = 1 := by
  apply Measure.ae_smul_measure
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  exact Filter.Eventually.of_forall fun x ↦ by simpa only [Metric.mem_sphere, dist_zero_right] using x.property

theorem isProbabilityMeasure_sphericalRowsLaw (m : ℕ) {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (sphericalRowsLaw m n) := by
  let := isProbabilityMeasure_sphericalLaw hn
  unfold sphericalRowsLaw
  infer_instance

theorem ae_sphericalRowsLaw_unitRows (m : ℕ) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ A ∂sphericalRowsLaw m n, UnitRows A := by
  let := isProbabilityMeasure_sphericalLaw hn
  apply (ae_all_iff).mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin m ↦ sphericalLaw n) i).quasiMeasurePreserving.ae
    (ae_sphericalLaw_norm n)

end NLA.RowDeletion

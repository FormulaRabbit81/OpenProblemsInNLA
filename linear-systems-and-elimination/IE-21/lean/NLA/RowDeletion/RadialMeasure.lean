import NLA.RowDeletion.Sphere
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Pi

/-! # Transport of radial densities through polar coordinates

The angular factor comes from Mathlib's Haar-to-sphere theorem. No formula for
the area of a sphere or for a Gamma integral is needed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NLA.RowDeletion

lemma map_withDensity_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hf, lintegral_withDensity_eq_lintegral_mul _ (hw.comp hf)
    (show Measurable (fun a ↦ g (f a)) from hg.comp hf),
    lintegral_withDensity_eq_lintegral_mul _ hw hg]
  exact (lintegral_map (hw.mul hg) hf).symm

lemma comap_subtype_withDensity
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (hs : MeasurableSet s) (w : α → ℝ≥0∞) :
    (μ.withDensity w).comap (fun x : s ↦ (x : α)) =
      (μ.comap (fun x : s ↦ (x : α))).withDensity (fun x ↦ w x) := by
  ext t ht
  rw [(MeasurableEmbedding.subtype_coe hs).comap_apply, withDensity_apply _
    ((MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr ht),
    withDensity_apply _ ht, setLIntegral_subtype hs]

theorem polar_map_radial_density (n : ℕ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (((volume : Measure (Vector n)).withDensity (fun x ↦ w ‖x‖)).comap
      (fun x : ({0}ᶜ : Set (Vector n)) ↦ (x : Vector n))).map
        (homeomorphUnitSphereProd (Vector n)) =
      (volume : Measure (Vector n)).toSphere.prod
        ((Measure.volumeIoiPow (Module.finrank ℝ (Vector n) - 1)).withDensity
          (fun r : Set.Ioi (0 : ℝ) ↦ w r)) := by
  rw [comap_subtype_withDensity _ (measurableSet_singleton _).compl]
  have he : (fun x : ({0}ᶜ : Set (Vector n)) ↦ w ‖(x : Vector n)‖) =
      (fun p : Metric.sphere (0 : Vector n) 1 × Set.Ioi (0 : ℝ) ↦ w p.2) ∘
        homeomorphUnitSphereProd (Vector n) := by
    funext x
    simp
  rw [he, map_withDensity_comp _ (homeomorphUnitSphereProd (Vector n)).measurable
    (w := fun p : Metric.sphere (0 : Vector n) 1 × Set.Ioi (0 : ℝ) ↦ w p.2)
    (by fun_prop),
    (volume : Measure (Vector n)).measurePreserving_homeomorphUnitSphereProd.map_eq]
  exact (prod_withDensity_right (g := fun r : Set.Ioi (0 : ℝ) ↦ w r)
    (by fun_prop)).symm

end NLA.RowDeletion

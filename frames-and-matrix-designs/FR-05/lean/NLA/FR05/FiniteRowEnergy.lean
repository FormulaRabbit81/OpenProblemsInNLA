/-
Finite-row tail lift for the source-coordinate energy event.
-/
import NLA.FR05.DerivativeNorm
import NLA.FR05.SourceMarginals
import NLA.FR05.SourceRowBridge
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace NLA.FR05

theorem iidSourceCoordinateLawAt_radial_tail_real
    {M m n : ℕ} (hM : 1 ≤ M) (i : Fin m) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | 8 * (M : ℝ) ≤ (p i).1.1} ≤
      25 * Real.exp (-(4 * (M : ℝ))) := by
  let μ0 : Measure (SourcePlantedCoordinates n) :=
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
  letI : IsProbabilityMeasure μ0 :=
    isProbabilityMeasure_sourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) n
  have hpres : MeasurePreserving (Function.eval i)
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) μ0 := by
    change MeasurePreserving (Function.eval i) (Measure.pi (fun _ : Fin m => μ0)) μ0
    exact measurePreserving_eval _ i
  let s : Set (SourcePlantedCoordinates n) := {p | 8 * (M : ℝ) ≤ p.1.1}
  have hs : MeasurableSet s := measurableSet_Ici.preimage (measurable_fst.comp measurable_fst)
  have hmeasure :
      iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n
          ((Function.eval i) ⁻¹' s) = μ0 s := by
    exact hpres.measure_preimage hs.nullMeasurableSet
  have htail : μ0 s ≤
      (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ)))) := by
    simpa [μ0, s] using sourceCoordinateLaw_sourceM_radial_tail n hM
  have hreal : μ0.real s ≤ 25 * Real.exp (-(4 * (M : ℝ))) := by
    rw [Measure.real_def]
    have h := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)).mpr htail
    simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  change (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
    ((Function.eval i) ⁻¹' s) ≤ _
  rw [Measure.real_def, hmeasure]
  exact hreal

theorem iidSourceCoordinateLawAt_tail_energy_tail_real
    {M m n : ℕ} (hM : 1 ≤ M) (i : Fin m) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | 8 * (n : ℝ) ≤ signalEnergy (p i).2} ≤
      Real.exp (-3 * (n : ℝ)) := by
  let μ0 : Measure (SourcePlantedCoordinates n) :=
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
  letI : IsProbabilityMeasure μ0 :=
    isProbabilityMeasure_sourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) n
  have hpres : MeasurePreserving (Function.eval i)
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) μ0 := by
    change MeasurePreserving (Function.eval i) (Measure.pi (fun _ : Fin m => μ0)) μ0
    exact measurePreserving_eval _ i
  let s : Set (SourcePlantedCoordinates n) :=
    {p | 8 * (n : ℝ) ≤ signalEnergy p.2}
  have hs : MeasurableSet s :=
    measurableSet_Ici.preimage (measurable_signalEnergy.comp measurable_snd)
  have hmeasure :
      iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n
          ((Function.eval i) ⁻¹' s) = μ0 s := by
    exact hpres.measure_preimage hs.nullMeasurableSet
  have htail : μ0 s ≤ ENNReal.ofReal (Real.exp (-3 * (n : ℝ))) := by
    simpa [μ0, s] using sourceCoordinateLaw_tail_energy_tail n sourceEta_pos.le
      sourceEta_lt_one (sourceEpsilon_pos M hM)
  have hreal : μ0.real s ≤ Real.exp (-3 * (n : ℝ)) := by
    rw [Measure.real_def]
    have h := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr htail
    simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  change (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
    ((Function.eval i) ⁻¹' s) ≤ _
  rw [Measure.real_def, hmeasure]
  exact hreal

theorem iidSourceCoordinateLawAt_tail_energy_tail_at_M_real
    {M m n : ℕ} (hM : 1 ≤ M) (hnM : n ≤ M) (i : Fin m) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | 8 * (M : ℝ) ≤ signalEnergy (p i).2} ≤
      Real.exp (-3 * (n : ℝ)) := by
  letI : IsProbabilityMeasure
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) :=
    isProbabilityMeasure_iidSourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) m n
  apply le_trans (measureReal_mono ?_)
    (iidSourceCoordinateLawAt_tail_energy_tail_real hM i)
  intro p hp
  change 8 * (M : ℝ) ≤ signalEnergy (p i).2 at hp
  change 8 * (n : ℝ) ≤ signalEnergy (p i).2
  have hnM' : (n : ℝ) ≤ M := by exact_mod_cast hnM
  linarith

/-- The source's coordinatewise tail estimates lift to the finite-row event
in (3.22), before converting source coordinates to checked planted rows. -/
theorem iidSourceCoordinateLawAt_row_energy_max_tail_real
    {M m n : ℕ} (hM : 1 ≤ M) (hnM : n ≤ M) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | ∃ i, 16 * (M : ℝ) ≤ (p i).1.1 + signalEnergy (p i).2} ≤
      m * (25 * Real.exp (-(4 * (M : ℝ))) + Real.exp (-3 * (n : ℝ))) := by
  letI : IsProbabilityMeasure
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) :=
    isProbabilityMeasure_iidSourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) m n
  exact row_energy_max_tail_of_component_tails
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n)
    m (M : ℝ) (25 * Real.exp (-(4 * (M : ℝ))))
    (Real.exp (-3 * (n : ℝ)))
    (fun i p => (p i).1.1) (fun i p => signalEnergy (p i).2)
    (fun i => iidSourceCoordinateLawAt_radial_tail_real hM i)
    (fun i => iidSourceCoordinateLawAt_tail_energy_tail_at_M_real hM hnM i)

end NLA.FR05

/-
Shared literal source-row small-ball event and almost-sure source support.

Both branches of Lemma 3.6 are first proved on reassociated source
coordinates. This small module keeps the actual row event and the support
facts in a neutral location for their later combination.
-/
import NLA.FR05.SourceTailBridge
import NLA.FR05.SourceMarginals
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The literal row-form small-ball event, using the total source-to-row map.
Off source support that map is harmless, while on support it is the actual row. -/
def sourceRowJacobianSmallBallEvent {n : ℕ}
    (p q : Signal n) (sigma b g u : ℝ) : Set (SourcePlantedCoordinates n) :=
  {x | |sourceRowJacobianForm (sourceCoordinatesToPlantedRowOrDefault x)
    sigma b g p q| ≤ u}

/-- All source-coordinate support conditions used by the source-row bridges
hold almost surely under the actual product law. -/
theorem ae_sourceCoordinateLaw_fullSupport
    {eta delta epsilon : ℝ} (n : ℕ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hepsilon1 : epsilon ≤ 1) :
    ∀ᵐ x ∂sourceCoordinateLaw eta delta epsilon n,
      0 < x.1.1 ∧ |x.1.2.1| ≤ 1 ∧
        x.1.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
        x.1.2.2.2 ∈ Icc 0 (2 * Real.pi) := by
  letI : IsProbabilityMeasure (sourceRadialLaw eta delta) :=
    isProbabilityMeasure_sourceRadialLaw heta0 heta1
  letI : IsProbabilityMeasure (sourceUniformInterval (-epsilon) epsilon) :=
    isProbabilityMeasure_sourceUniformInterval (by linarith)
  letI : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  letI : IsProbabilityMeasure (standardComplexGaussianTail n) :=
    isProbabilityMeasure_standardComplexGaussianTail n
  rw [sourceCoordinateLaw, sourceScalarLaw]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceRadialLaw_Ici heta0 heta1] with S hS
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceUniformInterval_self (by linarith : -epsilon < epsilon)] with xi hxi
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceUniformInterval_self (by positivity : 0 < 2 * Real.pi)] with alpha halpha
  filter_upwards [ae_mem_sourceUniformInterval_self (by positivity : 0 < 2 * Real.pi)] with beta hbeta
  filter_upwards with w
  exact ⟨lt_of_lt_of_le hdelta hS, (abs_le.2 hxi).trans hepsilon1, halpha, hbeta⟩

end NLA.FR05

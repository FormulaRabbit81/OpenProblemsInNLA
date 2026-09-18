/-
Conditional-product assembly for one source planted row.

The scalar coordinates and complex-Gaussian tail are independent in the
actual source law.  This makes the preceding product-section lemma directly
available for the tail conditional estimates in Lemma 3.6.
-/
import NLA.FR05.ProductSections
import NLA.FR05.PlantedLaw
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- A uniform conditional bound over the independent Gaussian tail holds for
the complete source-coordinate law of one planted row. -/
theorem sourceCoordinateLaw_le_of_tail_sections_le
    {η δ ε : ℝ} (n : ℕ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    {s : Set (SourcePlantedCoordinates n)} (hs : MeasurableSet s) (c : ℝ≥0∞)
    (hsection : ∀ q : SourcePlantedScalars,
      standardComplexGaussianTail n {w | (q, w) ∈ s} ≤ c) :
    sourceCoordinateLaw η δ ε n s ≤ c := by
  letI : IsProbabilityMeasure (sourceScalarLaw η δ ε) :=
    isProbabilityMeasure_sourceScalarLaw hη0 hη1 hε
  letI : IsProbabilityMeasure (standardComplexGaussianTail n) :=
    isProbabilityMeasure_standardComplexGaussianTail n
  unfold sourceCoordinateLaw
  exact prod_measure_le_of_sections_le (sourceScalarLaw η δ ε)
    (standardComplexGaussianTail n) hs c hsection

end NLA.FR05

/-
Measurable product decomposition of a finite iid source-coordinate sample.

This is the conditioning interface needed in the row-to-span part of
Lemma 3.7: one selected row is separated from all other rows while preserving
the actual source-coordinate product law.
-/
import NLA.FR05.SourceRowBridge
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLA.FR05

/-- Split a sample of `m + 1` source rows into row `i` and the remaining rows,
with the latter indexed through `Fin.succAbove i`. -/
noncomputable def iidSourceCoordinateSplit
    (m n : ℕ) (i : Fin (m + 1)) :
    (Fin (m + 1) → SourcePlantedCoordinates n) ≃ᵐ
      SourcePlantedCoordinates n × (Fin m → SourcePlantedCoordinates n) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => SourcePlantedCoordinates n) i

theorem iidSourceCoordinateSplit_fst_apply
    {m n : ℕ} (i : Fin (m + 1))
    (sample : Fin (m + 1) → SourcePlantedCoordinates n) :
    (iidSourceCoordinateSplit m n i sample).1 = sample i := rfl

theorem iidSourceCoordinateSplit_snd_apply
    {m n : ℕ} (i : Fin (m + 1))
    (sample : Fin (m + 1) → SourcePlantedCoordinates n) (j : Fin m) :
    (iidSourceCoordinateSplit m n i sample).2 j = sample (i.succAbove j) := rfl

/-- The source iid law is preserved by separating any one row from the other
`m` rows.  This is an exact finite-product identity, not an independence
heuristic. -/
theorem measurePreserving_iidSourceCoordinateSplit
    {η δ ε : ℝ} (m n : ℕ) (i : Fin (m + 1))
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    MeasurePreserving (iidSourceCoordinateSplit m n i)
      (iidSourceCoordinateLaw η δ ε (m + 1) n)
      ((sourceCoordinateLaw η δ ε n).prod (iidSourceCoordinateLaw η δ ε m n)) := by
  let _ : IsProbabilityMeasure (sourceCoordinateLaw η δ ε n) :=
    isProbabilityMeasure_sourceCoordinateLaw hη0 hη1 hε n
  change MeasurePreserving
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => SourcePlantedCoordinates n) i)
    (Measure.pi (fun _ : Fin (m + 1) => sourceCoordinateLaw η δ ε n))
    ((sourceCoordinateLaw η δ ε n).prod
      (Measure.pi (fun _ : Fin m => sourceCoordinateLaw η δ ε n)))
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => sourceCoordinateLaw η δ ε n) i

end NLA.FR05

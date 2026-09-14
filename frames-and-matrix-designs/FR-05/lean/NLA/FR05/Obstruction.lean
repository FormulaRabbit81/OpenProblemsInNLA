/-
The exact deterministic obstruction shared by Lemma 2.1 and the planted-law
part of Li's proof. No probability or quotient-space construction is used.
-/
import NLA.FR05.Definitions
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section

namespace NLA.FR05

theorem firstCoordinate_ne_secondCoordinate (d : ℕ) (hd : 2 ≤ d) :
    firstCoordinate d hd ≠ secondCoordinate d hd := by
  simp [firstCoordinate, secondCoordinate]

/-- Two signals with equal measurements that are not globally phased refute
injectivity of the original phase-retrieval predicate. -/
theorem not_phaseRetrievalInjective_of_witness {m d : ℕ} (A : Frame m d)
    (x y : Signal d) (hmeas : SameMeasurements A x y)
    (hnphase : ¬ GloballyPhased x y) :
    ¬ PhaseRetrievalInjective A := by
  intro hinj
  exact hnphase (hinj x y hmeas)

theorem flatFrame_measurements_equal {m d : ℕ} (i : Fin m) (j k : Fin d) :
    rowMagnitude (flatFrame m d) (standardBasis j) i =
      rowMagnitude (flatFrame m d) (standardBasis k) i := by
  simp [rowMagnitude, flatFrame, standardBasis]

/-- The first and second standard signals cannot differ by a unit complex
phase: evaluating a putative equality at the second coordinate gives `1 = 0`. -/
theorem standardBasis_first_not_globallyPhased_second (d : ℕ) (hd : 2 ≤ d) :
    ¬ GloballyPhased (standardBasis (firstCoordinate d hd))
      (standardBasis (secondCoordinate d hd)) := by
  intro hphase
  obtain ⟨θ, hθ⟩ := hphase
  have hsecond := congrFun hθ (secondCoordinate d hd)
  have hne : secondCoordinate d hd ≠ firstCoordinate d hd :=
    Ne.symm (firstCoordinate_ne_secondCoordinate d hd)
  simp [standardBasis, hne] at hsecond

/-- In every FR-05 ambient dimension there is an explicit frame with a
rank-two ambiguity. This is a kernel-checked base witness only; it is not the
open-neighbourhood or Gaussian-probability assertion of the manuscript. -/
theorem flatFrame_not_phaseRetrievalInjective (d : ℕ) (hd : 2 ≤ d) :
    ¬ PhaseRetrievalInjective (flatFrame (4 * d - 5) d) := by
  apply not_phaseRetrievalInjective_of_witness
    (flatFrame (4 * d - 5) d)
    (standardBasis (firstCoordinate d hd))
    (standardBasis (secondCoordinate d hd))
  · intro i
    exact flatFrame_measurements_equal i _ _
  · exact standardBasis_first_not_globallyPhased_second d hd

end NLA.FR05

/-
The exact deterministic obstruction shared by Lemma 2.1 and the planted-law
part of Li's proof. No probability or quotient-space construction is used.
-/
import NLA.FR05.Definitions
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
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

/-- The quadratic form of a rank-one Hermitian outer product is the squared
modulus of the associated linear functional. -/
theorem quadraticForm_vecMulVec {d : ℕ} (a x : Signal d) :
    quadraticForm (Matrix.vecMulVec x (star x)) a =
      (Complex.normSq (star a ⬝ᵥ x) : ℂ) := by
  rw [quadraticForm, Matrix.vecMulVec_mulVec]
  rw [op_smul_eq_smul, dotProduct_smul]
  rw [Matrix.star_dotProduct]
  simp only [Complex.normSq_eq_conj_mul_self, smul_eq_mul, starRingEnd_apply]

theorem quadraticForm_sub {d : ℕ} (a : Signal d)
    (Q R : Matrix (Fin d) (Fin d) ℂ) :
    quadraticForm (Q - R) a = quadraticForm Q a - quadraticForm R a := by
  simp only [quadraticForm, Matrix.sub_mulVec, dotProduct_sub]

/-- The quadratic form of `xxᴴ - yyᴴ` is the difference of the two squared
measurement moduli. -/
theorem quadraticForm_rankOneDifference {d : ℕ} (a x y : Signal d) :
    quadraticForm (rankOneDifference x y) a =
      (Complex.normSq (star a ⬝ᵥ x) - Complex.normSq (star a ⬝ᵥ y) : ℂ) := by
  rw [rankOneDifference, quadraticForm_sub, quadraticForm_vecMulVec,
    quadraticForm_vecMulVec]

/-- Rewriting a row measurement as the norm of its Hermitian linear
functional. -/
theorem rowMagnitude_eq_norm_dotProduct_conjugateRow {m d : ℕ}
    (A : Frame m d) (x : Signal d) (i : Fin m) :
    rowMagnitude A x i = ‖star (conjugateRow A i) ⬝ᵥ x‖ := by
  simp only [rowMagnitude, conjugateRow, star_star]
  rfl

/-- An all-row zero certificate for `xxᴴ - yyᴴ` produces identical
measurement moduli.  This is the exact deterministic bridge used at the end
of Proposition 3.1. -/
theorem sameMeasurements_of_rankOneDifference_quadraticForm_eq_zero
    {m d : ℕ} (A : Frame m d) (x y : Signal d)
    (hzero : ∀ i, quadraticForm (rankOneDifference x y) (conjugateRow A i) = 0) :
    SameMeasurements A x y := by
  intro i
  rw [rowMagnitude_eq_norm_dotProduct_conjugateRow,
    rowMagnitude_eq_norm_dotProduct_conjugateRow]
  have hq := hzero i
  rw [quadraticForm_rankOneDifference] at hq
  have hnormSq : Complex.normSq (star (conjugateRow A i) ⬝ᵥ x) =
      Complex.normSq (star (conjugateRow A i) ⬝ᵥ y) := by
    exact_mod_cast sub_eq_zero.mp hq
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hnormSq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormSq

/-- A rank-one-difference kernel certificate refutes phase-retrieval
injectivity whenever its two signals are genuinely distinct modulo phase. -/
theorem not_phaseRetrievalInjective_of_rankOneDifference_quadraticForm_eq_zero
    {m d : ℕ} (A : Frame m d) (x y : Signal d)
    (hzero : ∀ i, quadraticForm (rankOneDifference x y) (conjugateRow A i) = 0)
    (hnphase : ¬ GloballyPhased x y) :
    ¬ PhaseRetrievalInjective A := by
  apply not_phaseRetrievalInjective_of_witness A x y
  · exact sameMeasurements_of_rankOneDifference_quadraticForm_eq_zero A x y hzero
  · exact hnphase

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

/-
The affine-cosine phase estimate used in the first branch of Lemma 3.6.

After a phase normalization, the conditional tail variance has the form
`A + B * cos φ`, where `A ≥ 1 / 4`, `0 ≤ B ≤ A`.  This module turns the
canonical estimate in `PhaseSmallBall` into the uniform bound `4t` for its
sublevel probability.  The remaining task is to connect an arbitrary phase
shift in the variance profile to this normalized form.
-/
import NLA.FR05.PhaseSmallBall
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The one-period sublevel set for a nonnegative affine cosine profile. -/
def affineCosinePhaseSublevel (A B t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧
    A + B * Real.cos φ ≤ t ^ 2}

/-- If the constant term dominates the amplitude, an affine cosine sublevel
is contained in the corresponding canonical cosine sublevel. -/
theorem affineCosinePhaseSublevel_subset_canonical
    (A B t : ℝ) (hB : 0 < B) (hBA : B ≤ A) :
    affineCosinePhaseSublevel A B t ⊆
      cosinePhaseSublevel (t / Real.sqrt B) := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ A + B * Real.cos φ ≤ t ^ 2 at hφ
  constructor
  · exact hφ.1
  have hlower : B * (1 + Real.cos φ) ≤ A + B * Real.cos φ := by
    nlinarith [hBA]
  have hcanonical : B * (1 + Real.cos φ) ≤ t ^ 2 :=
    hlower.trans hφ.2
  have hdiv : 1 + Real.cos φ ≤ t ^ 2 / B := by
    apply (le_div_iff₀ hB).mpr
    simpa only [mul_comm] using hcanonical
  calc
    1 + Real.cos φ ≤ t ^ 2 / B := hdiv
    _ = (t / Real.sqrt B) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hB.le]

/-- The canonical probability estimate at an arbitrary positive amplitude. -/
theorem sourceUniformInterval_affineCosinePhaseSublevel_le
    (A B t : ℝ) (ht : 0 ≤ t) (hB : 0 < B) (hBA : B ≤ A) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) ≤
      ENNReal.ofReal (t / Real.sqrt B) := by
  calc
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) ≤
        sourceUniformInterval 0 (2 * Real.pi)
          (cosinePhaseSublevel (t / Real.sqrt B)) :=
      measure_mono (affineCosinePhaseSublevel_subset_canonical A B t hB hBA)
    _ ≤ ENNReal.ofReal (t / Real.sqrt B) :=
      sourceUniformInterval_cosinePhaseSublevel_le _
        (div_nonneg ht (Real.sqrt_nonneg B))

/-- A convenient numerical form once the amplitude is bounded below. -/
theorem sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul
    (A B t : ℝ) (ht : 0 ≤ t) (hB : 0 < B) (hBA : B ≤ A)
    (hBsmall : (1 / 16 : ℝ) ≤ B) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) ≤ ENNReal.ofReal (4 * t) := by
  have hrootlower : (1 / 4 : ℝ) ≤ Real.sqrt B := by
    apply (Real.le_sqrt (by norm_num) hB.le).mpr
    nlinarith [hBsmall]
  have hdiv : t / Real.sqrt B ≤ 4 * t := by
    calc
      t / Real.sqrt B ≤ t / (1 / 4 : ℝ) :=
        div_le_div_of_nonneg_left ht (by norm_num) hrootlower
      _ = 4 * t := by ring
  exact (sourceUniformInterval_affineCosinePhaseSublevel_le A B t ht hB hBA).trans
    (ENNReal.ofReal_le_ofReal hdiv)

/-- In the small-amplitude regime, a sufficiently low sublevel set is empty. -/
theorem affineCosinePhaseSublevel_subset_empty
    (A B t : ℝ) (hB : 0 ≤ B) (hBhalf : B ≤ A / 2)
    (ht : t ^ 2 < A / 2) :
    affineCosinePhaseSublevel A B t ⊆ ∅ := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ A + B * Real.cos φ ≤ t ^ 2 at hφ
  have hcos : -1 ≤ Real.cos φ := Real.neg_one_le_cos φ
  have hBcos : -B ≤ B * Real.cos φ := by
    calc
      -B = B * (-1) := by ring
      _ ≤ B * Real.cos φ := mul_le_mul_of_nonneg_left hcos hB
  have hlower : A / 2 ≤ A + B * Real.cos φ := by
    nlinarith [hBhalf, hBcos]
  exfalso
  exact (not_le_of_gt ht) (hlower.trans hφ.2)

/-- The source's affine-cosine phase bound: for `A ≥ 1/4` and
`0 ≤ B ≤ A`, the sublevel probability is at most `4t`. -/
theorem sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul_of_quarter
    (A B t : ℝ) (ht : 0 ≤ t) (hA : (1 / 4 : ℝ) ≤ A)
    (hB : 0 ≤ B) (hBA : B ≤ A) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) ≤ ENNReal.ofReal (4 * t) := by
  rcases le_total B (A / 2) with hBhalf | hhalfB
  · rcases lt_or_ge t (1 / 4 : ℝ) with htSmall | htLarge
    · have hquad : t ^ 2 < (1 / 4 : ℝ) ^ 2 := by
        have hpos : 0 < ((1 / 4 : ℝ) - t) * ((1 / 4 : ℝ) + t) :=
          mul_pos (sub_pos.mpr htSmall) (by linarith)
        nlinarith
      have hsmall : t ^ 2 < A / 2 := by
        nlinarith [hquad, hA]
      calc
        sourceUniformInterval 0 (2 * Real.pi)
            (affineCosinePhaseSublevel A B t) ≤
            sourceUniformInterval 0 (2 * Real.pi) ∅ :=
          measure_mono (affineCosinePhaseSublevel_subset_empty A B t hB hBhalf hsmall)
        _ = 0 := measure_empty
        _ ≤ ENNReal.ofReal (4 * t) := bot_le
    · letI : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
        isProbabilityMeasure_sourceUniformInterval (by positivity)
      calc
        sourceUniformInterval 0 (2 * Real.pi)
            (affineCosinePhaseSublevel A B t) ≤
            sourceUniformInterval 0 (2 * Real.pi) univ :=
          measure_mono (subset_univ _)
        _ = 1 := measure_univ
        _ = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal (4 * t) := ENNReal.ofReal_le_ofReal (by linarith)
  · have hBsmall : (1 / 16 : ℝ) ≤ B := by
      nlinarith [hA, hhalfB]
    have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hBsmall
    exact sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul
      A B t ht hBpos hBA hBsmall

end NLA.FR05

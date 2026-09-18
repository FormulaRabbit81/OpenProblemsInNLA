/-
Exact first- and second-order algebra for the polynomial factor chart.
This provides the Jacobian layer of the planted proof without introducing an
unnecessary transcendental coordinate change.
-/
import NLA.FR05.FactorChart
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

/-- The positive factor's tangent vector at the seed. -/
def plusDirection {n : ℕ} (s : ℝ) (b : ℂ) (z : Signal n) : Signal (n + 2) :=
  joinTwo (s / 4) (star b) z

/-- The negative factor's tangent vector at the seed. -/
def minusDirection {n : ℕ} (s : ℝ) (t : Signal n) : Signal (n + 2) :=
  joinTwo 0 (-s / 4) (-t)

/-- Along every real ray of chart parameters, the positive factor is exactly
affine. -/
theorem factorPlus_scaled {n : ℕ} (r s : ℝ) (b : ℂ) (z : Signal n) :
    factorPlus (r * s) (r • b) (r • z) =
      factorPlus (n := n) 0 0 0 + r • plusDirection s b z := by
  funext i
  by_cases hi0 : i.1 = 0
  · simp [factorPlus, plusDirection, joinTwo, hi0]
    ring
  · by_cases hi1 : i.1 = 1
    · simp [factorPlus, plusDirection, joinTwo, hi1]
    · simp [factorPlus, plusDirection, joinTwo, hi0, hi1]

/-- Along every real ray of chart parameters, the negative factor is exactly
affine. -/
theorem factorMinus_scaled {n : ℕ} (r s : ℝ) (t : Signal n) :
    factorMinus (r * s) (r • t) =
      factorMinus (n := n) 0 0 + r • minusDirection s t := by
  funext i
  by_cases hi0 : i.1 = 0
  · simp [factorMinus, minusDirection, joinTwo, hi0]
  · by_cases hi1 : i.1 = 1
    · simp [factorMinus, minusDirection, joinTwo, hi1]
      ring
    · simp [factorMinus, minusDirection, joinTwo, hi0, hi1]

/-- The linear part of the factor chart along a parameter ray. -/
def factorChartLinear {n : ℕ} (s : ℝ) (b : ℂ) (z t : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  Matrix.vecMulVec (plusDirection s b z) (star (factorPlus (n := n) 0 0 0)) +
    Matrix.vecMulVec (factorPlus (n := n) 0 0 0) (star (plusDirection s b z)) -
      Matrix.vecMulVec (minusDirection s t) (star (factorMinus (n := n) 0 0)) -
        Matrix.vecMulVec (factorMinus (n := n) 0 0) (star (minusDirection s t))

/-- The quadratic remainder of the factor chart along a parameter ray. -/
def factorChartQuadratic {n : ℕ} (s : ℝ) (b : ℂ) (z t : Signal n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  rankOneDifference (plusDirection s b z) (minusDirection s t)

/-- An exact Taylor identity for the chart.  In particular, its first
derivative at the seed is `factorChartLinear`, and all remaining terms are
quadratic. -/
theorem factorChart_scaled_expansion {n : ℕ} (r s : ℝ) (b : ℂ) (z t : Signal n) :
    factorChart (r * s) (r • b) (r • z) (r • t) =
      factorChart (n := n) 0 0 0 0 + r • factorChartLinear s b z t +
        r ^ 2 • factorChartQuadratic s b z t := by
  rw [factorChart, factorPlus_scaled, factorMinus_scaled]
  ext i j
  simp [factorChart, rankOneDifference, factorChartLinear, factorChartQuadratic,
    Matrix.vecMulVec, Pi.star_apply]
  ring

end NLA.FR05

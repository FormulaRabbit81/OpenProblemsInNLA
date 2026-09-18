/-
The exact Taylor expansion of the source's normalized measurement equations
in the polynomial factor chart.
-/
import NLA.FR05.Planted
import NLA.FR05.FactorTaylor
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix
noncomputable section

namespace NLA.FR05

theorem quadraticForm_add {d : ℕ} (a : Signal d)
    (Q R : Matrix (Fin d) (Fin d) ℂ) :
    quadraticForm (Q + R) a = quadraticForm Q a + quadraticForm R a := by
  simp [quadraticForm, Matrix.add_mulVec, dotProduct_add]

theorem quadraticForm_real_smul {d : ℕ} (a : Signal d)
    (r : ℝ) (Q : Matrix (Fin d) (Fin d) ℂ) :
    quadraticForm (r • Q) a = r • quadraticForm Q a := by
  simp [quadraticForm, Matrix.smul_mulVec, dotProduct_smul]

/-- The directional linear term of a planted measurement equation. -/
def plantedEquationLinear {n : ℕ} (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) : ℝ :=
  (quadraticForm (factorChartLinear s b z t) (plantedColumn row)).re / row.radial

/-- The exact directional quadratic remainder of a planted measurement
equation. -/
def plantedEquationQuadratic {n : ℕ} (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) : ℝ :=
  (quadraticForm (factorChartQuadratic s b z t) (plantedColumn row)).re / row.radial

/-- The planted measurement equations are exactly quadratic along every
parameter ray.  This is a source-specific, checked replacement for an
informal first-derivative calculation at the seed. -/
theorem plantedEquation_scaled_expansion {n : ℕ} (u : ℝ) (row : PlantedRow n)
    (s : ℝ) (b : ℂ) (z t : Signal n) :
    plantedEquation row (u * s) (u • b) (u • z) (u • t) =
      plantedEquation row 0 0 0 0 + u * plantedEquationLinear row s b z t +
        u ^ 2 * plantedEquationQuadratic row s b z t := by
  unfold plantedEquation plantedEquationLinear plantedEquationQuadratic
  rw [factorChart_scaled_expansion]
  rw [quadraticForm_add, quadraticForm_add,
    quadraticForm_real_smul, quadraticForm_real_smul]
  simp only [Complex.add_re, Complex.smul_re]
  ring

end NLA.FR05

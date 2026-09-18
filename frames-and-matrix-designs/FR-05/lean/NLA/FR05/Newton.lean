/-
The fixed-point endpoint used in the proof of Proposition 3.1.

This module records the Banach-contraction step separately from the
source-specific estimates which establish its hypotheses.  It is stated for
the planted equation map, so a fixed point is immediately an exact
phase-retrieval ambiguity through `Planted.lean`.
-/
import NLA.FR05.Planted
import NLA.FR05.SourceParameters
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate Matrix NNReal

namespace NLA.FR05

/-- The real coordinate space of the polynomial rank-two factor chart. -/
abbrev FactorParameters (n : ℕ) := ℝ × ℂ × Signal n × Signal n

/-- The real dimension of the chart coordinate space.  With `n = M - 2`,
this is the source row count `4M - 5`. -/
theorem finrank_factorParameters (n : ℕ) :
    Module.finrank ℝ (FactorParameters n) = 1 + 2 + 2 * n + 2 * n := by
  simp [FactorParameters, Complex.finrank_real_complex, Module.finrank_pi_fintype]
  omega

/-- At the source dimensions, the planted equation map has square real
Jacobian size. -/
theorem finrank_factorParameters_source (M : ℕ) (hM : 2 ≤ M) :
    Module.finrank ℝ (FactorParameters (sourceTailDimension M)) =
      sourceRowCount M := by
  rw [finrank_factorParameters]
  exact source_chart_real_parameter_count M hM

/-- The planted measurement map in the polynomial factor-chart coordinates. -/
def plantedEquationMap {m n : ℕ} (rows : Fin m → PlantedRow n) :
    FactorParameters n → (Fin m → ℝ) :=
  fun θ i ↦ plantedEquation (rows i) θ.1 θ.2.1 θ.2.2.1 θ.2.2.2

theorem plantedEquationMap_apply {m n : ℕ} (rows : Fin m → PlantedRow n)
    (θ : FactorParameters n) (i : Fin m) :
    plantedEquationMap rows θ i =
      plantedEquation (rows i) θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 := rfl

/-- `F^ε(0)` is exactly the vector of planted imbalances. -/
theorem plantedEquationMap_zero {m n : ℕ} (rows : Fin m → PlantedRow n) :
    plantedEquationMap rows 0 = fun i ↦ (rows i).imbalance := by
  funext i
  simp [plantedEquationMap, plantedEquation_zero]

/-- A coordinate of a point in the chart ball is bounded by the ball radius.
This is the small local-chart fact used to pass from the Newton ball to the
`|s| ≤ 1` hypothesis of the factor chart. -/
theorem abs_factorParameter_scalar_le_radius {n : ℕ}
    (θ : FactorParameters n) {R : ℝ}
    (hθ : θ ∈ Metric.closedBall (0 : FactorParameters n) R) :
    |θ.1| ≤ R := by
  rw [← Real.norm_eq_abs]
  calc
    ‖θ.1‖ ≤ ‖θ‖ := norm_fst_le θ
    _ = dist θ 0 := (dist_zero_right θ).symm
    _ ≤ R := Metric.mem_closedBall.mp hθ

/-- The Newton self-map associated to a chosen injective left inverse of the
linearization. -/
def plantedNewtonMap {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n) :
    FactorParameters n → FactorParameters n :=
  fun θ ↦ θ - Jinv (plantedEquationMap rows θ)

/-- A contraction of the source Newton map on a closed coordinate ball has a
zero of the planted equations in that ball.  This discharges the exact
fixed-point implication in Proposition 3.1 without assuming a root. -/
theorem exists_plantedEquationMap_zero_of_contracting
    {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n)
    (hJinj : Function.Injective Jinv)
    (R : ℝ) (hR : 0 ≤ R) (K : ℝ≥0)
    (hmap : Set.MapsTo (plantedNewtonMap rows Jinv)
      (Metric.closedBall (0 : FactorParameters n) R)
      (Metric.closedBall (0 : FactorParameters n) R))
    (hcontract : ContractingWith K
      (hmap.restrict (plantedNewtonMap rows Jinv)
        (Metric.closedBall (0 : FactorParameters n) R)
        (Metric.closedBall (0 : FactorParameters n) R))) :
    ∃ θ : FactorParameters n, θ ∈ Metric.closedBall 0 R ∧
      plantedEquationMap rows θ = 0 := by
  have hcomplete : IsComplete (Metric.closedBall (0 : FactorParameters n) R) :=
    Metric.isClosed_closedBall.isComplete
  have hzero : (0 : FactorParameters n) ∈ Metric.closedBall 0 R := by
    simp [hR]
  obtain ⟨θ, hθball, hfixed, -, -⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmap hzero (edist_ne_top _ _)
  refine ⟨θ, hθball, ?_⟩
  apply hJinj
  have hsub : Jinv (plantedEquationMap rows θ) = 0 := by
    exact sub_eq_self.mp hfixed
  simpa using hsub

/-- If the contraction ball keeps the scalar chart coordinate in the local
range used by the factor chart, the fixed point produces a genuine
non-injectivity witness for the planted frame. -/
theorem plantedFrame_not_phaseRetrievalInjective_of_contracting
    {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n)
    (hJinj : Function.Injective Jinv)
    (R : ℝ) (hR : 0 ≤ R) (K : ℝ≥0)
    (hmap : Set.MapsTo (plantedNewtonMap rows Jinv)
      (Metric.closedBall (0 : FactorParameters n) R)
      (Metric.closedBall (0 : FactorParameters n) R))
    (hcontract : ContractingWith K
      (hmap.restrict (plantedNewtonMap rows Jinv)
        (Metric.closedBall (0 : FactorParameters n) R)
        (Metric.closedBall (0 : FactorParameters n) R)))
    (hscalar : ∀ θ : FactorParameters n,
      θ ∈ Metric.closedBall 0 R → |θ.1| ≤ 1) :
    ¬ PhaseRetrievalInjective (plantedFrame rows) := by
  obtain ⟨θ, hθball, hzero⟩ := exists_plantedEquationMap_zero_of_contracting
    rows Jinv hJinj R hR K hmap hcontract
  exact plantedFrame_not_phaseRetrievalInjective_of_equations_eq_zero rows
    θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 (hscalar θ hθball) (by
      intro i
      exact congr_fun hzero i)

/-- The previous endpoint in the concrete source regime where the Newton
radius is at most one. -/
theorem plantedFrame_not_phaseRetrievalInjective_of_contracting_of_radius_le_one
    {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n)
    (hJinj : Function.Injective Jinv)
    (R : ℝ) (hR : 0 ≤ R) (hRone : R ≤ 1) (K : ℝ≥0)
    (hmap : Set.MapsTo (plantedNewtonMap rows Jinv)
      (Metric.closedBall (0 : FactorParameters n) R)
      (Metric.closedBall (0 : FactorParameters n) R))
    (hcontract : ContractingWith K
      (hmap.restrict (plantedNewtonMap rows Jinv)
        (Metric.closedBall (0 : FactorParameters n) R)
        (Metric.closedBall (0 : FactorParameters n) R))) :
    ¬ PhaseRetrievalInjective (plantedFrame rows) := by
  apply plantedFrame_not_phaseRetrievalInjective_of_contracting rows Jinv hJinj
    R hR K hmap hcontract
  intro θ hθ
  exact (abs_factorParameter_scalar_le_radius θ hθ).trans hRone

end NLA.FR05

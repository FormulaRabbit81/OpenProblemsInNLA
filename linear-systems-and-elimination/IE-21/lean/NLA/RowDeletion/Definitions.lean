import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Definitions shared by IE-21 and IE-22

The row-deletion quantities are defined by the original variational problem.
The spherical law is normalized surface measure, independently of the Gaussian
representation that will be proved later. No proof or challenge is imported here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace NLA.RowDeletion

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Rows (m n : ℕ) := Fin m → Vector n

def UnitRows {m n : ℕ} (A : Rows m n) : Prop := ∀ i, ‖A i‖ = 1

def retainedCount (θ : ℝ) (m : ℕ) : ℕ := ⌊θ * (m : ℝ)⌋₊

def retainedEnergy {m n : ℕ} (A : Rows m n) (S : Finset (Fin m))
    (x : Vector n) : ℝ := ∑ i ∈ S, (inner ℝ (A i) x) ^ 2

/-- The squared variational least singular value after exactly `floor (θ*m)` rows
are retained. Its equivalence to the original minimum of norms is a proof obligation. -/
def trimmedEnergy {m n : ℕ} (θ : ℝ) (A : Rows m n) : ℝ :=
  sInf {v | ∃ S : Finset (Fin m), S.card = retainedCount θ m ∧
    ∃ x : Vector n, ‖x‖ = 1 ∧ v = retainedEnergy A S x}

/-- The original variational minimum, with no full-rank assumption. -/
def deletionSingularValue {m n : ℕ} (θ : ℝ) (A : Rows m n) : ℝ :=
  sInf {v | ∃ S : Finset (Fin m), S.card = retainedCount θ m ∧
    ∃ x : Vector n, ‖x‖ = 1 ∧ v = Real.sqrt (retainedEnergy A S x)}

def rowOperator {m n : ℕ} (A : Rows m n) : Vector n →L[ℝ] Vector m :=
  (Matrix.toEuclideanLin (fun i j ↦ A i j)).toContinuousLinearMap

/-- The induced Euclidean operator norm, not the default norm on matrix entries. -/
def operatorNorm {m n : ℕ} (A : Rows m n) : ℝ := ‖rowOperator A‖

def normalizedTrimmedEnergy {m n : ℕ} (θ : ℝ) (A : Rows m n) : ℝ :=
  (n : ℝ) / m * trimmedEnergy θ A

def normalizedOperatorEnergy {m n : ℕ} (A : Rows m n) : ℝ :=
  (n : ℝ) / m * operatorNorm A ^ 2

def deletionRatio {m n : ℕ} (θ : ℝ) (A : Rows m n) : ℝ :=
  deletionSingularValue θ A ^ 2 / operatorNorm A ^ 2

def normalizedDeletion {m n : ℕ} (θ : ℝ) (A : Rows m n) : ℝ :=
  Real.sqrt ((n : ℝ) / m) * deletionSingularValue θ A

def extremalDeletion (θ : ℝ) (m n : ℕ) : ℝ :=
  sSup {v | ∃ A : Rows m n, UnitRows A ∧ v = normalizedDeletion θ A}

/-- Surface measure on the unit sphere, normalized before mapping to the ambient space.
Only positive dimensions are used in the advertised probability statements. -/
def sphericalLaw (n : ℕ) : Measure (Vector n) :=
  let σ := (volume : Measure (Vector n)).toSphere
  (σ Set.univ)⁻¹ • σ.map (fun u : Metric.sphere (0 : Vector n) 1 ↦ (u : Vector n))

/-- Independent rows, each with the normalized surface law. -/
def sphericalRowsLaw (m n : ℕ) : Measure (Rows m n) :=
  Measure.pi (fun _ : Fin m ↦ sphericalLaw n)

/-- Explicit specification of the Gaussian cutoff. Existence and uniqueness are
separate exported obligations, rather than assumptions hidden in a chosen constant. -/
def GaussianCutoff (θ a : ℝ) : Prop :=
  0 < a ∧ (gaussianReal 0 1).real (Set.Icc (-a) a) = θ

def gaussianTrimmedMoment (a : ℝ) : ℝ :=
  ∫ t in Set.Icc (-a) a, t ^ 2 ∂gaussianReal 0 1

def hinge (t y : ℝ) : ℝ := max (t - y) 0

def finiteThreshold {m : ℕ} (k : ℕ) (y : Fin m → ℝ) (t : ℝ) : ℝ :=
  (k : ℝ) * t - ∑ i, hinge t (y i)

def populationThreshold {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ℝ) (Y : Ω → ℝ) (t : ℝ) : ℝ :=
  θ * t - ∫ ω, hinge t (Y ω) ∂μ

def populationTrimmedMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ : ℝ) (Y : Ω → ℝ) : ℝ :=
  sSup (populationThreshold μ θ Y '' Set.Ici 0)

end NLA.RowDeletion

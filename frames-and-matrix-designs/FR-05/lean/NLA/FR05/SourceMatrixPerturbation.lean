/-
Finite-sample aggregation of the source-row `J_epsilon - J_0` estimate.

The frozen matrix `sourceJacobianMatrixFromCoordinates` represents `J_0`.
This file defines the corresponding actual seed-linearization map and
aggregates the rowwise imbalance bound on the source good event.
-/
import NLA.FR05.ImbalancePerturbation
import NLA.FR05.SourceGoodEvent
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

open scoped BigOperators ComplexConjugate Matrix RealInnerProductSpace

/-- The actual seed-linearization map `J_epsilon` in the real source
coordinates.  Its `i`th output is the normalized planted equation
linearization for the actual (possibly imbalanced) row. -/
def sourceEpsilonJacobianApply {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : SourceJacobianVector n) : SourceJacobianVector n :=
  fun i => plantedEquationLinear (sourceRowsFromCoordinates sample (e i))
    (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
    (sourceJacobianP x) (sourceJacobianQ x)

/-- The direction factor left by the conservative rowwise comparison. -/
def sourceJacobianDirectionFactor {n : ℕ}
    (x : SourceJacobianVector n) : ℝ :=
  ‖factorPlus (n := n) 0 0 0‖ *
      ‖plusDirection (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
        (sourceJacobianP x)‖ +
    ‖factorMinus (n := n) 0 0‖ *
      ‖minusDirection (x .sigma) (sourceJacobianQ x)‖

theorem sourceJacobianDirectionFactor_nonneg {n : ℕ}
    (x : SourceJacobianVector n) : 0 ≤ sourceJacobianDirectionFactor x := by
  unfold sourceJacobianDirectionFactor
  positivity

/-- The `J_epsilon` output is compared coordinatewise with the frozen
matrix action. -/
theorem abs_sourceEpsilonJacobianApply_sub_sourceJacobianMatrix_apply_le
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    |sourceEpsilonJacobianApply e sample x i -
        (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i| ≤
      2 * ((n + 2 : ℕ) : ℝ) ^ 2 *
        (Real.sqrt ((sourceRowsFromCoordinates sample (e i)).radial / 2) *
          |(sourceRowsFromCoordinates sample (e i)).imbalance|) *
        (‖plantedColumn (sourceRowsFromCoordinates sample (e i))‖ +
          ‖plantedColumn (sourceRowsFromCoordinates sample (e i)).zeroImbalance‖) /
            (sourceRowsFromCoordinates sample (e i)).radial *
        sourceJacobianDirectionFactor x := by
  unfold sourceEpsilonJacobianApply
  rw [sourceJacobianMatrixFromCoordinates_mulVec_apply]
  simpa [sourceRowsFromCoordinates, sourceJacobianDirectionFactor] using
    (abs_plantedEquationLinear_sub_sourceRowJacobianForm_le
      (sourceRowsFromCoordinates sample (e i)) (x .sigma) (x .beta) (x .gamma)
      (sourceJacobianP x) (sourceJacobianQ x))

/-- A finite Euclidean vector with all coordinates bounded by `C` has norm
at most `sqrt(card) C`. -/
theorem euclideanNorm_le_sqrt_card_mul_of_abs_le
    {ι : Type*} [Fintype ι] (v : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, |v i| ≤ C) :
    ‖WithLp.toLp 2 v‖ ≤ Real.sqrt (Fintype.card ι) * C := by
  have hsquares : ∀ i, v i ^ 2 ≤ C ^ 2 := by
    intro i
    have habs := hv i
    have hsq : |v i| ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hC).mpr habs
    simpa only [sq_abs] using hsq
  have hsum : ∑ i, v i ^ 2 ≤ (Fintype.card ι : ℝ) * C ^ 2 := by
    calc
      ∑ i, v i ^ 2 ≤ ∑ _i : ι, C ^ 2 :=
        Finset.sum_le_sum fun i _ => hsquares i
      _ = (Fintype.card ι : ℝ) * C ^ 2 := by simp
  have hleft : 0 ≤ ‖WithLp.toLp 2 v‖ := norm_nonneg _
  have hright : 0 ≤ Real.sqrt (Fintype.card ι) * C :=
    mul_nonneg (Real.sqrt_nonneg _) hC
  apply (sq_le_sq₀ hleft hright).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, v i ^ 2 ≤ (Fintype.card ι : ℝ) * C ^ 2 := hsum
    _ = (Real.sqrt (Fintype.card ι) * C) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- On the finite source good event, each coordinate of `J_epsilon x-J_0 x`
has the explicit source-scale bound supplied by the rowwise comparison.
The separate imbalance hypothesis is the almost-sure support fact with the
sharper width `sourceEpsilon M`; `SourceCoordinateSampleGood` itself stores
only the weaker `|xi| ≤ 1` needed to construct rows. -/
theorem abs_sourceEpsilonJacobianApply_sub_sourceJacobianMatrix_apply_le_good
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x : SourceJacobianVector n) (i : SourceJacobianCoordinate n) :
    |sourceEpsilonJacobianApply e sample x i -
        (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i| ≤
      4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
        sourceDelta M * sourceEpsilon M * sourceJacobianDirectionFactor x := by
  have hi := hgood (e i)
  have hrow := sourceCoordinatesToPlantedRowOrDefault_eq_of_good hM
    (sample (e i)) hi
  let r : PlantedRow n := sourceCoordinatesToPlantedRow (sample (e i))
    (lt_of_lt_of_le (sourceDelta_pos M (by omega)) hi.1) hi.2.1
  have hradial : sourceDelta M ≤ r.radial := by
    change sourceDelta M ≤ (sample (e i)).1.1
    exact hi.1
  have henergy : r.radial + squaredEuclideanNorm r.tail ≤ 16 * (M : ℝ) := by
    change (sample (e i)).1.1 + squaredEuclideanNorm (sample (e i)).2 ≤
      16 * (M : ℝ)
    simpa [signalEnergy] using hi.2.2
  have hsmall : |r.imbalance| ≤ sourceEpsilon M := by
    change |(sample (e i)).1.2.1| ≤ sourceEpsilon M
    exact himbalance (e i)
  unfold sourceEpsilonJacobianApply
  rw [sourceJacobianMatrixFromCoordinates_mulVec_apply]
  change |plantedEquationLinear (sourceRowsFromCoordinates sample (e i))
      (x .sigma) ((x .beta : ℂ) + (x .gamma) * Complex.I)
      (sourceJacobianP x) (sourceJacobianQ x) -
      sourceRowJacobianForm (sourceRowsFromCoordinates sample (e i))
        (x .sigma) (x .beta) (x .gamma)
        (sourceJacobianP x) (sourceJacobianQ x)| ≤ _
  rw [sourceRowsFromCoordinates, hrow]
  simpa [r, sourceJacobianDirectionFactor] using
    (abs_plantedEquationLinear_sub_sourceRowJacobianForm_le_of_radial_tail
      r
      (x .sigma) (x .beta) (x .gamma) (sourceJacobianP x) (sourceJacobianQ x)
      (sourceDelta_pos M (by omega)) hradial henergy hsmall)

/-- Euclidean aggregation of the source-good-event row bound.  This is the
finite-sample `J_epsilon - J_0` estimate before bounding the chart-direction
factor by the Euclidean norm of the input. -/
theorem euclideanNorm_sourceEpsilonJacobianError_le_good
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x : SourceJacobianVector n) :
    ‖WithLp.toLp 2 (fun i : SourceJacobianCoordinate n =>
        sourceEpsilonJacobianApply e sample x i -
          (sourceJacobianMatrixFromCoordinates e sample *ᵥ x) i)‖ ≤
      Real.sqrt (Fintype.card (SourceJacobianCoordinate n)) *
        (4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
          sourceDelta M * sourceEpsilon M * sourceJacobianDirectionFactor x) := by
  apply euclideanNorm_le_sqrt_card_mul_of_abs_le
  · have hdelta : 0 < sourceDelta M := sourceDelta_pos M (by omega)
    have hepsilon : 0 ≤ sourceEpsilon M :=
      (sourceEpsilon_pos M (by omega)).le
    have hMreal : 0 ≤ (M : ℝ) := by positivity
    have hnum : 0 ≤ 4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) := by
      positivity
    have hfrac : 0 ≤
        4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) / sourceDelta M :=
      div_nonneg hnum hdelta.le
    exact mul_nonneg (mul_nonneg hfrac hepsilon)
      (sourceJacobianDirectionFactor_nonneg x)
  · intro i
    exact abs_sourceEpsilonJacobianApply_sub_sourceJacobianMatrix_apply_le_good
      hM e sample hgood himbalance x i

/-- The actual `J_epsilon` map on the Euclidean coordinate space used by the
least-gain formulation. -/
def sourceEpsilonJacobianEuclideanApply {m n : ℕ}
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    EuclideanSpace ℝ (SourceJacobianCoordinate n) :=
  WithLp.toLp 2 (sourceEpsilonJacobianApply e sample (WithLp.ofLp x))

/-- Exact identification of the Euclidean-map error with the coordinatewise
error vector aggregated above. -/
theorem sourceEpsilonJacobianEuclideanApply_sub_frozen_eq
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    sourceEpsilonJacobianEuclideanApply e sample x -
        euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x =
      WithLp.toLp 2 (fun i : SourceJacobianCoordinate n =>
        sourceEpsilonJacobianApply e sample (WithLp.ofLp x) i -
          (sourceJacobianMatrixFromCoordinates e sample *ᵥ WithLp.ofLp x) i) := by
  rfl

/-- Euclidean-map form of the finite-sample perturbation estimate. -/
theorem norm_sourceEpsilonJacobianEuclideanApply_sub_frozen_le_good
    {M m n : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n)
    (hgood : SourceCoordinateSampleGood M sample)
    (himbalance : ∀ j, |(sample j).1.2.1| ≤ sourceEpsilon M)
    (x : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    ‖sourceEpsilonJacobianEuclideanApply e sample x -
        euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x‖ ≤
      Real.sqrt (Fintype.card (SourceJacobianCoordinate n)) *
        (4 * ((n + 2 : ℕ) : ℝ) ^ 2 * (16 * (M : ℝ)) /
          sourceDelta M * sourceEpsilon M *
            sourceJacobianDirectionFactor (WithLp.ofLp x)) := by
  rw [sourceEpsilonJacobianEuclideanApply_sub_frozen_eq]
  exact euclideanNorm_sourceEpsilonJacobianError_le_good
    hM e sample hgood himbalance (WithLp.ofLp x)

/-- Deterministic lower-gain transfer across a `kappa / 2` Euclidean map
perturbation. -/
theorem euclidean_lower_bound_transfer_of_half_perturbation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    {κ : ℝ} (hzero : HasEuclideanLowerBound A κ)
    (hperturb : ∀ x, ‖G x - euclideanMap A x‖ ≤ (κ / 2) * ‖x‖) :
    ∀ x, (κ / 2) * ‖x‖ ≤ ‖G x‖ := by
  intro x
  have hzero_x := hzero x
  have hperturb_x := hperturb x
  have htriangle :
      ‖euclideanMap A x‖ ≤ ‖G x‖ + ‖G x - euclideanMap A x‖ := by
    calc
      ‖euclideanMap A x‖ = ‖G x - (G x - euclideanMap A x)‖ := by
        congr 1
        abel
      _ ≤ ‖G x‖ + ‖G x - euclideanMap A x‖ := norm_sub_le _ _
  linarith

/-- Specialized lower-gain transfer from the frozen source matrix `J_0` to
the actual source seed-linearization `J_epsilon`. -/
theorem sourceEpsilonJacobian_lower_bound_transfer_of_half_perturbation
    {m n : ℕ} (e : SourceJacobianCoordinate n ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates n) {κ : ℝ}
    (hzero : HasEuclideanLowerBound (sourceJacobianMatrixFromCoordinates e sample) κ)
    (hperturb : ∀ x,
      ‖sourceEpsilonJacobianEuclideanApply e sample x -
          euclideanMap (sourceJacobianMatrixFromCoordinates e sample) x‖ ≤
        (κ / 2) * ‖x‖) :
    ∀ x, (κ / 2) * ‖x‖ ≤ ‖sourceEpsilonJacobianEuclideanApply e sample x‖ := by
  exact euclidean_lower_bound_transfer_of_half_perturbation
    (sourceJacobianMatrixFromCoordinates e sample)
    (sourceEpsilonJacobianEuclideanApply e sample) hzero hperturb

end NLA.FR05

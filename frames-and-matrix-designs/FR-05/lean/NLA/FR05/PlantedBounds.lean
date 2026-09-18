/-
Finite-dimensional norm estimates for the planted equation map.

The norm in this file is the actual Euclidean norm (rather than Lean's
default sup norm on a finite function type), matching the vector norm in
equation (3.24) of the source.
-/
import NLA.FR05.Newton
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace NLA.FR05

/-- Euclidean norm on a finite real coordinate vector. -/
def realEuclideanNorm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

theorem realEuclideanNorm_nonneg {m : ℕ} (x : Fin m → ℝ) :
    0 ≤ realEuclideanNorm x :=
  Real.sqrt_nonneg _

theorem sq_realEuclideanNorm {m : ℕ} (x : Fin m → ℝ) :
    realEuclideanNorm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold realEuclideanNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- A coordinatewise interval bound gives the usual Euclidean $ℓ^2$
bound. -/
theorem realEuclideanNorm_le_of_abs_le {m : ℕ} (x : Fin m → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hx : ∀ i, |x i| ≤ ε) :
    realEuclideanNorm x ≤ ε * Real.sqrt m := by
  have hsquares : ∀ i, x i ^ 2 ≤ ε ^ 2 := by
    intro i
    have habs : 0 ≤ |x i| := abs_nonneg _
    have hbound := hx i
    rw [← sq_abs]
    nlinarith
  have hsum : ∑ i, x i ^ 2 ≤ (m : ℝ) * ε ^ 2 := by
    calc
      ∑ i, x i ^ 2 ≤ ∑ _i : Fin m, ε ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ hsquares i
      _ = (m : ℝ) * ε ^ 2 := by simp
  have hleft : 0 ≤ realEuclideanNorm x := realEuclideanNorm_nonneg x
  have hright : 0 ≤ ε * Real.sqrt m :=
    mul_nonneg hε (Real.sqrt_nonneg _)
  have hsqrtSq : (Real.sqrt (m : ℝ)) ^ 2 = m := by
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hsum' : realEuclideanNorm x ^ 2 ≤ (m : ℝ) * ε ^ 2 := by
    rwa [sq_realEuclideanNorm]
  nlinarith

/-- The source's $F^ε(0)$ estimate: when every planted imbalance lies in
`[-ε, ε]`, its exact initial residual has Euclidean norm at most
`ε √m`. -/
theorem plantedEquationMap_zero_euclideanNorm_le
    {m n : ℕ} (rows : Fin m → PlantedRow n) (ε : ℝ) (hε : 0 ≤ ε)
    (himbalance : ∀ i, |(rows i).imbalance| ≤ ε) :
    realEuclideanNorm (plantedEquationMap rows 0) ≤ ε * Real.sqrt m := by
  rw [plantedEquationMap_zero]
  exact realEuclideanNorm_le_of_abs_le (fun i ↦ (rows i).imbalance) ε hε himbalance

end NLA.FR05

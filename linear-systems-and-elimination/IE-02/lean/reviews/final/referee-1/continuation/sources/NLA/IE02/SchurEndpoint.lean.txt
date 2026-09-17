/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's Euclidean coordinate norm, nonnegative finite sums,
polynomial degree, and finite-dimensional submodule APIs.

The norm-one constant coefficient exhausts the first column's squared norm.
Only the coefficients visible in the finite matrix are forced to vanish;
the symbol itself has no assumed degree bound.
-/
import NLA.IE02.Toeplitz
import NLA.IE02.MaximalSpace
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators Matrix
open Polynomial

theorem schur_scalar_endpoint {n : ℕ} (hn : 1 ≤ n) (p : Poly)
    (hU : operatorNorm (toeplitz n p) = 1) (hc : ‖p.coeff 0‖ = 1) :
    toeplitz n p = p.coeff 0 • 1 ∧
    SchurPair n (toeplitz n p) 0 (C (p.coeff 0)) 1 := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let e : H n := PiLp.single 2 i0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hcolumn (i : Fin n) : (euclideanLin (toeplitz n p) e) i = p.coeff i.val := by
    -- Expose the Euclidean matrix action on the first coordinate vector.
    change (∑ j : Fin n, toeplitz n p i j * e j) = p.coeff i.val
    simp [e, PiLp.single_apply, toeplitz, i0]
    intro hi
    exact (Nat.not_lt_zero i.val hi).elim
  have hbound : ‖euclideanLin (toeplitz n p) e‖ ≤ 1 := by
    calc
      ‖euclideanLin (toeplitz n p) e‖ ≤ operatorNorm (toeplitz n p) * ‖e‖ :=
        (euclideanCLM (toeplitz n p)).le_opNorm e
      _ = 1 := by rw [hU, he, one_mul]
  have hsum : (∑ i : Fin n, ‖p.coeff i.val‖ ^ 2) ≤ 1 := by
    calc
      (∑ i : Fin n, ‖p.coeff i.val‖ ^ 2) = ‖euclideanLin (toeplitz n p) e‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [hcolumn]
      _ ≤ 1 := by
        simpa only [one_pow] using
          (sq_le_sq₀ (norm_nonneg (euclideanLin (toeplitz n p) e))
            (zero_le_one : (0 : ℝ) ≤ 1)).mpr hbound
  have hsplit :
      1 + (∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, ‖p.coeff i.val‖ ^ 2) =
        ∑ i : Fin n, ‖p.coeff i.val‖ ^ 2 := by
    have hfirst : ‖p.coeff i0.val‖ ^ 2 = (1 : ℝ) := by
      -- The first finite index has natural value zero.
      change ‖p.coeff 0‖ ^ 2 = 1
      rw [hc]
      norm_num
    calc
      1 + (∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, ‖p.coeff i.val‖ ^ 2) =
          ‖p.coeff i0.val‖ ^ 2 +
            (∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, ‖p.coeff i.val‖ ^ 2) := by
        rw [hfirst]
      _ = ∑ i : Fin n, ‖p.coeff i.val‖ ^ 2 :=
        Finset.add_sum_erase (Finset.univ : Finset (Fin n))
          (fun i => ‖p.coeff i.val‖ ^ 2) (Finset.mem_univ i0)
  have hnonneg :
      0 ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, ‖p.coeff i.val‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg ‖p.coeff i.val‖
  have hzero :
      (∑ i ∈ (Finset.univ : Finset (Fin n)).erase i0, ‖p.coeff i.val‖ ^ 2) = 0 := by
    linarith
  have hcoeff (i : Fin n) (hi : i ≠ i0) : p.coeff i.val = 0 := by
    have his : i ∈ (Finset.univ : Finset (Fin n)).erase i0 :=
      Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have hsqi :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n)).erase i0)
        (f := fun j : Fin n => ‖p.coeff j.val‖ ^ 2)
        (fun j _ => sq_nonneg ‖p.coeff j.val‖)).mp hzero i his
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsqi)
  have hscalar : toeplitz n p = p.coeff 0 • (1 : Square n) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [toeplitz]
    · by_cases hji : j.val ≤ i.val
      · have hpos : 0 < i.val - j.val := by
          have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
          omega
        have hlt : i.val - j.val < n := (Nat.sub_le _ _).trans_lt i.is_lt
        let r : Fin n := ⟨i.val - j.val, hlt⟩
        have hr : r ≠ i0 := by
          intro h
          have heq := congrArg Fin.val h
          dsimp [r, i0] at heq
          omega
        have hrzero : p.coeff (i.val - j.val) = 0 := hcoeff r hr
        simp [toeplitz, hji, hij, hrzero]
      · simp [toeplitz, hji, hij]
  have hcne : p.coeff 0 ≠ 0 := by
    intro h
    simp [h] at hc
  have haction (x : H n) : euclideanLin (toeplitz n p) x = p.coeff 0 • x := by
    rw [hscalar]
    -- Expose the existing Euclidean matrix map; scalar identity acts by scalar multiplication.
    change (Matrix.toLpLin 2 2 (p.coeff 0 • (1 : Square n))) x = p.coeff 0 • x
    rw [map_smul, Matrix.toLpLin_one]
    rfl
  have hall (x : H n) : x ∈ maximalSpace (toeplitz n p) := by
    apply ((maximal_space_norm (toeplitz n p)).2 x).mpr
    rw [haction, norm_smul, hc, hU]
  have htop : maximalSpace (toeplitz n p) = ⊤ := by
    apply top_unique
    intro x _hx
    exact hall x
  refine ⟨hscalar, ?_⟩
  refine ⟨by omega, ?_, ?_, ?_, isCoprime_one_right, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_zero] using Polynomial.degree_C hcne
  · exact Polynomial.degree_one_le
  · simp
  · intro z _hz
    simp [hc]
  · intro z _hz
    simp [hc]
  · rw [toeplitz_one, mul_one, toeplitz_C]
    exact hscalar
  · intro x
    constructor
    · intro _hx
      obtain ⟨hround, hdeg⟩ := (coefficient_roundtrip n).1 x
      refine ⟨vectorPolynomial x, ?_, ?_⟩
      · rcases hdeg with hzero | hdeg
        · simp [hzero, DegreeLE]
        · exact Polynomial.degree_le_of_natDegree_le (by omega)
      · simpa only [one_mul] using hround.symm
    · intro _hx
      exact hall x
  · intro h _hh
    rw [one_mul, hscalar, ← toeplitz_C, toeplitz_action, coeffVector_mul_truncate]
  · rw [htop, _root_.finrank_top, finrank_euclideanSpace_fin, Nat.sub_zero]

#print axioms schur_scalar_endpoint
#assert_trust kernel schur_scalar_endpoint

end
end NLA.IE02

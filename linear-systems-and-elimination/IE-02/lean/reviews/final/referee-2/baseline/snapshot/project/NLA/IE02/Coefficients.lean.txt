/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original problem and special-case attribution
to Tichý, Liesen, and Faber, the Faber–Liesen–Tichý approximation background, and
the Courtney–Sarason interpolation background are retained. The Polynomial.ofFn
coefficient APIs are reused from Mathlib, authored by Fabrizio Barroero.

Finite complex coefficient roundtrips and the actual Euclidean inner product.
Dimension zero and the fixed reflection bound are retained throughout.
-/
import NLA.IE02.Definitions
import Mathlib.Algebra.Polynomial.OfFn
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators Classical
open Polynomial

theorem vectorPolynomial_eq_ofFn {n : ℕ} (x : H n) :
    vectorPolynomial x = Polynomial.ofFn n (fun i => x i) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [vectorPolynomial, Polynomial.C_mul_X_pow_eq_monomial]

theorem coefficient_roundtrip (n : ℕ) :
    (∀ x : H n, coeffVector n (vectorPolynomial x) = x ∧
      DegreeLT (vectorPolynomial x) n) ∧
    (∀ p : Poly, DegreeLT p n → vectorPolynomial (coeffVector n p) = p) := by
  constructor
  · intro x
    constructor
    · apply PiLp.ext
      intro i
      -- coeffVector is WithLp.toLp of the coefficient function, so its
      -- application has exactly this coefficient, with the Euclidean norm intact.
      change (vectorPolynomial x).coeff i.val = x i
      rw [vectorPolynomial_eq_ofFn,
        Polynomial.ofFn_coeff_eq_val_of_lt (fun j => x j) i.is_lt]
    · -- At n=0 the zero-polynomial branch supplies DegreeLT; no false
      -- assertion about natDegree 0 being strictly below zero is needed.
      by_cases hx : vectorPolynomial x = 0
      · exact Or.inl hx
      · apply Or.inr
        apply (Polynomial.natDegree_lt_iff_degree_lt hx).mpr
        rw [vectorPolynomial_eq_ofFn]
        exact Polynomial.ofFn_degree_lt _
  · intro p hp
    rcases hp with rfl | hp
    · simp [vectorPolynomial, coeffVector]
    · rw [vectorPolynomial_eq_ofFn]
      -- The underlying function of coeffVector is precisely Polynomial.toFn;
      -- this change only exposes the two existing coefficient wrappers.
      change Polynomial.ofFn n (Polynomial.toFn n p) = p
      exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hp

theorem coefficient_inner_product (n N : ℕ) (p q : Poly) (hp : DegreeLE p N) :
    ‖coeffVector n p‖ ^ 2 = ∑ i : Fin n, ‖p.coeff i.val‖ ^ 2 ∧
    (conjReflect N p * q).coeff N =
      inner ℂ (coeffVector (N + 1) p) (coeffVector (N + 1) q) := by
  clear hp
  constructor
  · simpa only [coeffVector, PiLp.toLp_apply] using
      EuclideanSpace.norm_sq_eq (coeffVector n p)
  · -- Coefficient N sees only indices through N. The frozen degree
    -- hypothesis is retained; this identity needs no higher-coefficient bound.
    calc
      (conjReflect N p * q).coeff N =
          ∑ ij ∈ Finset.antidiagonal N,
            (conjReflect N p).coeff ij.2 * q.coeff ij.1 := by
        rw [Polynomial.coeff_mul]
        exact (Finset.Nat.sum_antidiagonal_swap
          (f := fun ij => (conjReflect N p).coeff ij.1 * q.coeff ij.2)).symm
      _ = ∑ i ∈ Finset.range (N + 1),
          (conjReflect N p).coeff (N - i) * q.coeff i :=
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => (conjReflect N p).coeff j * q.coeff i) N
      _ = ∑ i : Fin (N + 1), star (p.coeff i.val) * q.coeff i.val := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        rw [conjReflect, Polynomial.coeff_reflect,
          Polynomial.revAt_le (Nat.sub_le N i.val),
          Nat.sub_sub_self (Nat.le_of_lt_succ i.is_lt), Polynomial.coeff_map]
        rfl
      _ = inner ℂ (coeffVector (N + 1) p) (coeffVector (N + 1) q) := by
        simp only [PiLp.inner_apply, coeffVector,
          RCLike.inner_apply', starRingEnd_apply]

#print axioms coefficient_roundtrip
#assert_trust kernel coefficient_roundtrip
#print axioms coefficient_inner_product
#assert_trust kernel coefficient_inner_product

end
end NLA.IE02

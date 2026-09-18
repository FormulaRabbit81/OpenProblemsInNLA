/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library attribution
is retained in Definitions.lean, Coefficients.lean, and SourceCorrespondence.md.
The Matrix.toLpLin equivalence APIs are reused from Mathlib's module by Eric Wieser.

The concrete coefficient matrix acts by truncated polynomial multiplication.
The algebra laws are proved from that action before constructing an algebra hom.
All vector spaces have their actual Euclidean interpretation, including dimension zero.
-/
import NLA.IE02.Coefficients

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators Classical Matrix
open Polynomial

theorem toeplitz_action {n : ℕ} (p : Poly) (x : H n) :
    euclideanLin (toeplitz n p) x = coeffVector n (p * vectorPolynomial x) := by
  apply PiLp.ext
  intro i
  -- Matrix.toLpLin at exponent two is definitionally multiplication of the
  -- coordinate vector. This exposes one row without changing its normed space.
  change (∑ j : Fin n, toeplitz n p i j * x j) =
    (p * vectorPolynomial x).coeff i.val
  rw [vectorPolynomial, Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← mul_assoc, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_C]
  by_cases h : j.val ≤ i.val <;> simp [toeplitz, h]

theorem vectorPolynomial_coeffVector_coeff {n : ℕ} (q : Poly) {i : ℕ}
    (hi : i < n) :
    (vectorPolynomial (coeffVector n q)).coeff i = q.coeff i := by
  exact congrArg (fun x : H n => x ⟨i, hi⟩)
    ((coefficient_roundtrip n).1 (coeffVector n q)).1

theorem coeffVector_mul_truncate (n : ℕ) (p q : Poly) :
    coeffVector n (p * vectorPolynomial (coeffVector n q)) =
      coeffVector n (p * q) := by
  apply PiLp.ext
  intro i
  -- The coefficient-vector wrappers have precisely these scalar coordinates.
  change (p * vectorPolynomial (coeffVector n q)).coeff i.val = (p * q).coeff i.val
  simp only [Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u.1 + u.2 = i.val := Finset.mem_antidiagonal.mp hu
  have hu2 : u.2 < n := by omega
  rw [vectorPolynomial_coeffVector_coeff q hu2]

theorem toeplitz_zero (n : ℕ) : toeplitz n (0 : Poly) = 0 := by
  ext i j
  simp [toeplitz]

theorem toeplitz_one (n : ℕ) : toeplitz n (1 : Poly) = 1 := by
  apply (Matrix.toLpLin 2 2 : Square n ≃ₗ[ℂ] (H n →ₗ[ℂ] H n)).injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLpLin_one, LinearMap.id_apply]
  -- euclideanLin abbreviates this same Matrix.toLpLin map at exponent two.
  change euclideanLin (toeplitz n (1 : Poly)) x = x
  rw [toeplitz_action, one_mul]
  exact ((coefficient_roundtrip n).1 x).1

theorem toeplitz_add (n : ℕ) (p q : Poly) :
    toeplitz n (p + q) = toeplitz n p + toeplitz n q := by
  ext i j
  by_cases h : j.val ≤ i.val <;> simp [toeplitz, h]

theorem toeplitz_mul (n : ℕ) (p q : Poly) :
    toeplitz n (p * q) = toeplitz n p * toeplitz n q := by
  apply (Matrix.toLpLin 2 2 : Square n ≃ₗ[ℂ] (H n →ₗ[ℂ] H n)).injective
  rw [Matrix.toLpLin_mul_same]
  apply LinearMap.ext
  intro x
  -- The linear-map composition is the successive action on the same H n.
  change euclideanLin (toeplitz n (p * q)) x =
    euclideanLin (toeplitz n p) (euclideanLin (toeplitz n q) x)
  calc
    euclideanLin (toeplitz n (p * q)) x =
        coeffVector n ((p * q) * vectorPolynomial x) := toeplitz_action _ _
    _ = coeffVector n (p * (q * vectorPolynomial x)) := by rw [mul_assoc]
    _ = coeffVector n (p * vectorPolynomial (coeffVector n (q * vectorPolynomial x))) :=
      (coeffVector_mul_truncate n p (q * vectorPolynomial x)).symm
    _ = euclideanLin (toeplitz n p) (euclideanLin (toeplitz n q) x) := by
      rw [toeplitz_action, toeplitz_action]

theorem toeplitz_C_mul (n : ℕ) (c : ℂ) (p : Poly) :
    toeplitz n (C c * p) = c • toeplitz n p := by
  ext i j
  by_cases h : j.val ≤ i.val <;> simp [toeplitz, h]

theorem toeplitz_C (n : ℕ) (c : ℂ) : toeplitz n (C c) = c • 1 := by
  simpa only [mul_one, toeplitz_one] using toeplitz_C_mul n c (1 : Poly)

/-- The already-proved coefficient-matrix laws, packaged for polynomial reuse. -/
def toeplitzAlgHom (n : ℕ) : Poly →ₐ[ℂ] Square n where
  toFun := toeplitz n
  map_zero' := toeplitz_zero n
  map_one' := toeplitz_one n
  map_add' := toeplitz_add n
  map_mul' := toeplitz_mul n
  commutes' c := by
    -- The scalar embedding in Polynomial is C; the matrix embedding is c • 1.
    change toeplitz n (C c) = algebraMap ℂ (Square n) c
    rw [toeplitz_C, Algebra.algebraMap_eq_smul_one]

theorem toeplitzAlgHom_eq_aeval (n : ℕ) :
    toeplitzAlgHom n = Polynomial.aeval (shift n) := by
  apply Polynomial.algHom_ext
  -- The image of X under the concrete coefficient matrix is the frozen shift.
  change shift n = Polynomial.aeval (shift n) (X : Poly)
  exact (Polynomial.aeval_X _).symm

theorem polyEval_shift (n : ℕ) (p : Poly) : polyEval p (shift n) = toeplitz n p := by
  exact (AlgHom.congr_fun (toeplitzAlgHom_eq_aeval n) p).symm

theorem shift_pow_nilpotent (n : ℕ) : shift n ^ n = 0 := by
  have hmap : toeplitz n ((X : Poly) ^ n) = shift n ^ n :=
    map_pow (toeplitzAlgHom n) (X : Poly) n
  rw [← hmap]
  ext i j
  have hlt : i.val - j.val < n := (Nat.sub_le _ _).trans_lt i.is_lt
  simp [toeplitz, Polynomial.coeff_X_pow, ne_of_lt hlt]

theorem toeplitz_algebra (n : ℕ) (p q : Poly) (c : ℂ) :
    toeplitz n (1 : Poly) = 1 ∧
    toeplitz n (p + q) = toeplitz n p + toeplitz n q ∧
    toeplitz n (p * q) = toeplitz n p * toeplitz n q ∧
    toeplitz n (C c * p) = c • toeplitz n p ∧
    shift n ^ n = 0 ∧ polyEval p (shift n) = toeplitz n p := by
  exact ⟨toeplitz_one n, toeplitz_add n p q, toeplitz_mul n p q,
    toeplitz_C_mul n c p, shift_pow_nilpotent n, polyEval_shift n p⟩

#print axioms toeplitz_action
#assert_trust kernel toeplitz_action
#print axioms toeplitz_algebra
#assert_trust kernel toeplitz_algebra

end
end NLA.IE02

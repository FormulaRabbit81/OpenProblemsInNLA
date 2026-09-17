/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md.
The finite coefficient APIs reuse Mathlib's Polynomial.ofFn by Fabrizio Barroero.

The actual effective polynomial has the prescribed Fourier coefficients and
fixed-bound reflection. All m and ell are allowed, including ell=0.
-/
import NLA.IE02.FourierCoefficients
import Mathlib.Algebra.Polynomial.OfFn

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem effectivePolynomial_eq_ofFn {l : ℕ} (m ell : ℕ) (q : Fin l → Poly) :
    effectivePolynomial m ell q = Polynomial.ofFn (2 * ell + 1)
      (fun i => fourierCoeff m q ((i.val : ℤ) - (ell : ℤ))) := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [effectivePolynomial, Polynomial.C_mul_X_pow_eq_monomial]

theorem effective_coeff_le {l : ℕ} (m ell : ℕ) (q : Fin l → Poly)
    (i : ℕ) (hi : i ≤ 2 * ell) :
    (effectivePolynomial m ell q).coeff i = fourierCoeff m q ((i : ℤ) - (ell : ℤ)) := by
  rw [effectivePolynomial_eq_ofFn,
    Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_of_le hi)]

theorem effective_coeff_gt {l : ℕ} (m ell : ℕ) (q : Fin l → Poly)
    (i : ℕ) (hi : 2 * ell < i) : (effectivePolynomial m ell q).coeff i = 0 := by
  rw [effectivePolynomial_eq_ofFn]
  exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt hi)

theorem effective_degree_le {l : ℕ} (m ell : ℕ) (q : Fin l → Poly) :
    DegreeLE (effectivePolynomial m ell q) (2 * ell) := by
  apply Polynomial.degree_le_of_natDegree_le
  rw [effectivePolynomial_eq_ofFn]
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)

theorem effective_extreme_coefficients {l : ℕ} (m ell : ℕ) (q : Fin l → Poly)
    (hc : fourierCoeff m q (ell : ℤ) ≠ 0) :
    (effectivePolynomial m ell q).degree = (2 * ell : WithBot ℕ) ∧
      (effectivePolynomial m ell q).coeff 0 ≠ 0 := by
  have htop : (effectivePolynomial m ell q).coeff (2 * ell) ≠ 0 := by
    rw [effective_coeff_le m ell q (2 * ell) le_rfl]
    have hfreq : ((2 * ell : ℕ) : ℤ) - (ell : ℤ) = (ell : ℤ) := by omega
    rw [hfreq]
    exact hc
  refine ⟨Polynomial.degree_eq_of_le_of_coeff_ne_zero (effective_degree_le m ell q) htop, ?_⟩
  rw [effective_coeff_le m ell q 0 (Nat.zero_le _)]
  simp only [Int.natCast_zero, zero_sub, fourier_conjugate_symmetry]
  exact star_ne_zero.mpr hc

theorem effective_self_reflection {l : ℕ} (m ell : ℕ) (q : Fin l → Poly) :
    conjReflect (2 * ell) (effectivePolynomial m ell q) = effectivePolynomial m ell q := by
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ 2 * ell
  · rw [conjReflect, Polynomial.coeff_reflect, Polynomial.revAt_le hi,
      Polynomial.coeff_map, starRingEnd_apply,
      effective_coeff_le m ell q (2 * ell - i) (Nat.sub_le _ _),
      effective_coeff_le m ell q i hi]
    have hfreq : ((2 * ell - i : ℕ) : ℤ) - (ell : ℤ) = -((i : ℤ) - (ell : ℤ)) := by
      omega
    rw [hfreq, fourier_conjugate_symmetry, star_star]
  · have hgt : 2 * ell < i := Nat.lt_of_not_ge hi
    rw [conjReflect, Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hgt,
      Polynomial.coeff_map, starRingEnd_apply, effective_coeff_gt m ell q i hgt, star_zero]

#print axioms effective_extreme_coefficients
#assert_trust kernel effective_extreme_coefficients
#print axioms effective_self_reflection
#assert_trust kernel effective_self_reflection

end
end NLA.IE02

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library attribution
is retained in Definitions.lean, Coefficients.lean, Reflection.lean, Toeplitz.lean,
and SourceCorrespondence.md. In particular, this reuses Damiano Testa's polynomial
reflection foundations and Eric Wieser's matrix linear-equivalence APIs.

A supplied scalar factor identity preserves Euclidean coefficient norms and
full complex Toeplitz pairings. The real weights need not be nonnegative here.
-/
import NLA.IE02.Toeplitz
import NLA.IE02.Reflection
import Mathlib.Data.Complex.BigOperators

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators
open Polynomial

/-- Extract one complex coefficient identity before specializing to norms or directions. -/
private theorem weighted_polynomial_pairing {l : ℕ} (d m : ℕ)
    (f b h r : Poly) (q : Fin l → Poly) (w : Fin l → ℝ)
    (hf : DegreeLE f d) (hh : DegreeLE h m) (hq : ∀ j, DegreeLE (q j) m)
    (hfactor : h * conjReflect m h = ∑ j, C (w j : ℂ) * (q j * conjReflect m (q j))) :
    inner ℂ (coeffVector (d + m + 1) (f * h))
        (coeffVector (d + m + 1) (r * (b * h))) =
      ∑ j, (w j : ℂ) * inner ℂ (coeffVector (d + m + 1) (f * q j))
        (coeffVector (d + m + 1) (r * (b * q j))) := by
  let s : Poly := conjReflect d f * r * b
  have hdegree (g : Poly) (hg : DegreeLE g m) : DegreeLE (f * g) (d + m) := by
    simpa only [DegreeLE, Nat.cast_add] using Polynomial.degree_mul_le_of_le hf hg
  have hcoeff (g : Poly) (hg : DegreeLE g m) :
      inner ℂ (coeffVector (d + m + 1) (f * g))
          (coeffVector (d + m + 1) (r * (b * g))) =
        (s * (g * conjReflect m g)).coeff (d + m) := by
    rw [← (coefficient_inner_product (d + m + 1) (d + m)
      (f * g) (r * (b * g)) (hdegree g hg)).2,
      reflection_product d m f g hf hg]
    dsimp only [s]
    apply congrArg (fun p : Poly => p.coeff (d + m))
    ac_rfl
  calc
    inner ℂ (coeffVector (d + m + 1) (f * h))
        (coeffVector (d + m + 1) (r * (b * h))) =
        (s * (h * conjReflect m h)).coeff (d + m) := hcoeff h hh
    _ = (s * ∑ j, C (w j : ℂ) * (q j * conjReflect m (q j))).coeff (d + m) := by
      rw [hfactor]
    _ = ∑ j, (w j : ℂ) * (s * (q j * conjReflect m (q j))).coeff (d + m) := by
      rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [mul_left_comm s (C (w j : ℂ)), Polynomial.coeff_C_mul]
    _ = ∑ j, (w j : ℂ) * inner ℂ (coeffVector (d + m + 1) (f * q j))
        (coeffVector (d + m + 1) (r * (b * q j))) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← hcoeff (q j) (hq j)]

theorem weighted_coefficient_preservation {l k : ℕ} (d m : ℕ)
    (a b h : Poly) (q : Fin l → Poly) (w : Fin l → ℝ) (r : Fin k → Poly)
    (ha : DegreeLE a d) (hb : DegreeLE b d) (hh : DegreeLE h m)
    (hq : ∀ j, DegreeLE (q j) m)
    (hfactor : h * conjReflect m h = ∑ j, C (w j : ℂ) * (q j * conjReflect m (q j))) :
    ‖coeffVector (d + m + 1) (b * h)‖ ^ 2 =
      ∑ j, w j * ‖coeffVector (d + m + 1) (b * q j)‖ ^ 2 ∧
    ∀ i, inner ℂ (coeffVector (d + m + 1) (a * h))
        (euclideanLin (toeplitz (d + m + 1) (r i)) (coeffVector (d + m + 1) (b * h))) =
      ∑ j, (w j : ℂ) * inner ℂ (coeffVector (d + m + 1) (a * q j))
        (euclideanLin (toeplitz (d + m + 1) (r i)) (coeffVector (d + m + 1) (b * q j))) := by
  constructor
  · -- Only the norm conclusion takes real parts of the full complex identity.
    have hnorm := weighted_polynomial_pairing d m b b h 1 q w hb hh hq hfactor
    simp only [one_mul] at hnorm
    have hreal := congrArg Complex.re hnorm
    have hself (x : H (d + m + 1)) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    simpa only [Complex.re_sum, Complex.re_ofReal_mul, hself] using hreal
  · intro i
    -- The existing truncation bridge retains arbitrary degrees of r i.
    simp_rw [toeplitz_action, coeffVector_mul_truncate]
    exact weighted_polynomial_pairing d m a b h (r i) q w ha hh hq hfactor

#print axioms weighted_coefficient_preservation
#assert_trust kernel weighted_coefficient_preservation

end
end NLA.IE02

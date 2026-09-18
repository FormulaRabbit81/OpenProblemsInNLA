/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses the proved strict factorization, common-root reduction, weighted fold,
fixed-bound circle identity and polynomial uniqueness on the infinite circle.

Common circle factors are removed by decreasing the degree bound. Empty and
all-zero families are included, and no vanishing circle factor is canceled.
-/
import NLA.IE02.StrictFactorization
import NLA.IE02.CommonCircleRoot
import NLA.IE02.CircleUniqueness
import Mathlib.Data.Complex.BigOperators

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators
open Polynomial

private theorem unweighted_scalar_factorization {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (hq : ∀ j, DegreeLE (q j) m) :
    ∃ h : Poly, DegreeLE h m ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖h.eval z‖ ^ 2 = sumSquares q z := by
  classical
  have hall : ∀ m l : ℕ, ∀ q : Fin l → Poly, (∀ j, DegreeLE (q j) m) →
      ∃ h : Poly, DegreeLE h m ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖h.eval z‖ ^ 2 = sumSquares q z := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro l q hq
      by_cases hzero : ∀ j, q j = 0
      · refine ⟨0, ?_, ?_⟩
        · simp [DegreeLE]
        · intro z _hz
          simp [sumSquares, hzero]
      · have hne : ∃ j, q j ≠ 0 := not_forall.mp hzero
        by_cases hno : ∀ z : ℂ, ‖z‖ = 1 → ∃ j, (q j).eval z ≠ 0
        · exact strict_scalar_factorization m q hq hno
        · push Not at hno
          obtain ⟨ζ, hζ, hroot⟩ := hno
          obtain ⟨hm, r, hr⟩ := common_circle_root_reduction m q hq hne ζ hζ hroot
          obtain ⟨s, hs, hseval⟩ :=
            ih (m - 1) (by omega) l r (fun j => (hr j).2)
          refine ⟨(X - C ζ) * s, ?_, ?_⟩
          · have hprod : DegreeLE ((X - C ζ) * s) (1 + (m - 1)) := by
              simpa only [DegreeLE, Nat.cast_add, Nat.cast_one] using
                Polynomial.degree_mul_le_of_le (Polynomial.degree_X_sub_C ζ).le hs
            have hbound : 1 + (m - 1) = m := by omega
            simpa only [hbound] using hprod
          · intro z hz
            calc
              ‖((X - C ζ) * s).eval z‖ ^ 2 = ‖z - ζ‖ ^ 2 * ‖s.eval z‖ ^ 2 := by
                rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
                  Polynomial.eval_C, norm_mul, mul_pow]
              _ = ‖z - ζ‖ ^ 2 * sumSquares r z := by rw [hseval z hz]
              _ = sumSquares q z := by
                -- Multiplication, rather than cancellation, includes the point z=ζ.
                unfold sumSquares
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                rw [(hr j).1, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
                  Polynomial.eval_C, norm_mul, mul_pow]
  exact hall m l q hq

theorem weighted_scalar_factorization {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (w : Fin l → ℝ) (hq : ∀ j, DegreeLE (q j) m) (hw : ∀ j, 0 ≤ w j) :
    ∃ h : Poly, DegreeLE h m ∧
      (∀ z : ℂ, ‖z‖ = 1 → ‖h.eval z‖ ^ 2 = ∑ j, w j * ‖(q j).eval z‖ ^ 2) ∧
      h * conjReflect m h = ∑ j, C (w j : ℂ) * (q j * conjReflect m (q j)) := by
  obtain ⟨hfolddegree, hfoldeval⟩ := weighted_fold m q w hq hw
  obtain ⟨h, hh, heval⟩ :=
    unweighted_scalar_factorization m (fun j => weightedFold (w j) (q j)) hfolddegree
  have hweighted (z : ℂ) (hz : ‖z‖ = 1) :
      ‖h.eval z‖ ^ 2 = ∑ j, w j * ‖(q j).eval z‖ ^ 2 :=
    (heval z hz).trans (hfoldeval z)
  refine ⟨h, hh, hweighted, ?_⟩
  apply (circle_polynomial_uniqueness _ _).2
  intro z hz
  rw [circle_reflection_square m h hh z hz]
  -- Every reflection uses the same frozen bound m, including degree slack.
  calc
    z ^ m * ((‖h.eval z‖ ^ 2 : ℝ) : ℂ) =
        z ^ m * ((∑ j, w j * ‖(q j).eval z‖ ^ 2 : ℝ) : ℂ) := by rw [hweighted z hz]
    _ = ∑ j, (w j : ℂ) * (z ^ m * ((‖(q j).eval z‖ ^ 2 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Complex.ofReal_mul]
      ring
    _ = (∑ j, C (w j : ℂ) * (q j * conjReflect m (q j))).eval z := by
      rw [Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Polynomial.eval_mul, Polynomial.eval_C, circle_reflection_square m (q j) (hq j) z hz]

#print axioms weighted_scalar_factorization
#assert_trust kernel weighted_scalar_factorization

end
end NLA.IE02

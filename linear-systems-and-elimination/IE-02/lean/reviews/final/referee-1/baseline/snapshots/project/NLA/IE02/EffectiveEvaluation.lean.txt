/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md.

Embed the smaller frequency range using Fintype.sum_of_injective. The omitted
terms vanish by their actual Fourier coefficients. No analytic approximation.
-/
import NLA.IE02.FourierSupport
import NLA.IE02.EffectiveCoefficients

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem fourier_restrict_sum {l : ℕ} (m ell : ℕ) (q : Fin l → Poly)
    (hle : ell ≤ m)
    (hband : ∀ r : ℤ, r < -(ell : ℤ) ∨ (ell : ℤ) < r → fourierCoeff m q r = 0)
    (z : ℂ) :
    (∑ i : Fin (2 * ell + 1),
      fourierCoeff m q ((i.val : ℤ) - (ell : ℤ)) * z ^ ((i.val : ℤ) - (ell : ℤ))) =
    ∑ r : Fin (2 * m + 1),
      fourierCoeff m q ((r.val : ℤ) - (m : ℤ)) * z ^ ((r.val : ℤ) - (m : ℤ)) := by
  let e : Fin (2 * ell + 1) → Fin (2 * m + 1) :=
    fun i => ⟨i.val + (m - ell), by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp only [e] at hv
    omega
  apply Fintype.sum_of_injective e he
  · intro r hr
    have hout : (r.val : ℤ) - (m : ℤ) < -(ell : ℤ) ∨
        (ell : ℤ) < (r.val : ℤ) - (m : ℤ) := by
      by_contra h
      apply hr
      have hb : r.val - (m - ell) < 2 * ell + 1 := by omega
      refine ⟨⟨r.val - (m - ell), hb⟩, ?_⟩
      apply Fin.ext
      dsimp only [e]
      omega
    rw [hband _ hout, zero_mul]
  · intro i
    have hf : ((e i).val : ℤ) - (m : ℤ) = (i.val : ℤ) - (ell : ℤ) := by
      dsimp only [e]
      omega
    rw [hf]

theorem effective_evaluation {l : ℕ} (m ell : ℕ) (q : Fin l → Poly)
    (hq : ∀ j, DegreeLE (q j) m) (hle : ell ≤ m)
    (hband : ∀ r : ℤ, r < -(ell : ℤ) ∨ (ell : ℤ) < r → fourierCoeff m q r = 0)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (effectivePolynomial m ell q).eval z = z ^ ell * (sumSquares q z : ℂ) := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
  have hpower (i : Fin (2 * ell + 1)) :
      z ^ ell * z ^ ((i.val : ℤ) - (ell : ℤ)) = z ^ i.val := by
    have hindex : (ell : ℤ) + ((i.val : ℤ) - (ell : ℤ)) = (i.val : ℤ) := by omega
    calc
      z ^ ell * z ^ ((i.val : ℤ) - (ell : ℤ)) =
          z ^ ((ell : ℤ) + ((i.val : ℤ) - (ell : ℤ))) := by
        rw [zpow_add₀ hz0, zpow_natCast]
      _ = z ^ i.val := by rw [hindex, zpow_natCast]
  calc
    (effectivePolynomial m ell q).eval z =
        ∑ i : Fin (2 * ell + 1),
          fourierCoeff m q ((i.val : ℤ) - (ell : ℤ)) * z ^ i.val := by
      simp only [effectivePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    _ = z ^ ell * ∑ i : Fin (2 * ell + 1),
          fourierCoeff m q ((i.val : ℤ) - (ell : ℤ)) * z ^ ((i.val : ℤ) - (ell : ℤ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← hpower i]
      ring
    _ = z ^ ell * ∑ r : Fin (2 * m + 1),
          fourierCoeff m q ((r.val : ℤ) - (m : ℤ)) * z ^ ((r.val : ℤ) - (m : ℤ)) := by
      rw [fourier_restrict_sum m ell q hle hband z]
    _ = z ^ ell * (sumSquares q z : ℂ) := by
      rw [← (fourier_semantics m q hq).2.2 z hz]

#print axioms fourier_restrict_sum
#assert_trust kernel fourier_restrict_sum
#print axioms effective_evaluation
#assert_trust kernel effective_evaluation

end
end NLA.IE02

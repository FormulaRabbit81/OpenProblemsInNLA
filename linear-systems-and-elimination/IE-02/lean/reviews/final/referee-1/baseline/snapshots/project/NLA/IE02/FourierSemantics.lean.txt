/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md.

The complete frozen Fourier contract, using exact finite sums for every l and m.
-/
import NLA.IE02.FourierEvaluation

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem fourier_semantics {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (hq : ∀ j, DegreeLE (q j) m) :
    (∀ r : ℤ, fourierCoeff m q (-r) = star (fourierCoeff m q r)) ∧
    fourierCoeff m q 0 = ((∑ j, ∑ i : Fin (m + 1), ‖(q j).coeff i.val‖ ^ 2 : ℝ) : ℂ) ∧
    (∀ z : ℂ, ‖z‖ = 1 → (sumSquares q z : ℂ) =
      ∑ r : Fin (2 * m + 1),
        fourierCoeff m q ((r.val : ℤ) - (m : ℤ)) * z ^ ((r.val : ℤ) - (m : ℤ))) := by
  refine ⟨fourier_conjugate_symmetry m q, fourier_zero_coefficient m q, ?_⟩
  intro z hz
  classical
  calc
    (sumSquares q z : ℂ) =
        ∑ j, ∑ u : Fin (m + 1), ∑ v : Fin (m + 1),
          (q j).coeff u.val * star ((q j).coeff v.val) *
            z ^ ((u.val : ℤ) - (v.val : ℤ)) := by
      simp only [sumSquares, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      exact polynomial_norm_square_terms m (q j) (hq j) z hz
    _ = _ := by
      symm
      simp only [fourierCoeff, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      exact (fourier_frequency_select m u v
        ((q j).coeff u.val * star ((q j).coeff v.val)) z).symm

#print axioms fourier_semantics
#assert_trust kernel fourier_semantics

end
end NLA.IE02

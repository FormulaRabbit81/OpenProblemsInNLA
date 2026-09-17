/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical and library attribution
is retained in Definitions.lean and SourceCorrespondence.md.

The complete effective-polynomial contract, with an actual nonzero extreme
frequency and exact nonvanishing on the entire complex unit circle.
-/
import NLA.IE02.EffectiveEvaluation

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem effective_factor_polynomial {l : ℕ} (m : ℕ) (q : Fin l → Poly)
    (hq : ∀ j, DegreeLE (q j) m)
    (hno : ∀ z : ℂ, ‖z‖ = 1 → ∃ j, (q j).eval z ≠ 0) :
    ∃ ell : ℕ, ell ≤ m ∧
      (effectivePolynomial m ell q).degree = (2 * ell : WithBot ℕ) ∧
      (effectivePolynomial m ell q).coeff 0 ≠ 0 ∧
      conjReflect (2 * ell) (effectivePolynomial m ell q) = effectivePolynomial m ell q ∧
      (∀ z : ℂ, ‖z‖ = 1 →
        (effectivePolynomial m ell q).eval z = z ^ ell * (sumSquares q z : ℂ) ∧
        (effectivePolynomial m ell q).eval z ≠ 0) := by
  obtain ⟨ell, hle, hc, hband⟩ :=
    fourier_effective_band m q (fourier_zero_ne_zero m q hq hno)
  obtain ⟨hdegree, hc0⟩ := effective_extreme_coefficients m ell q hc
  refine ⟨ell, hle, hdegree, hc0, effective_self_reflection m ell q, ?_⟩
  intro z hz
  have heval := effective_evaluation m ell q hq hle hband z hz
  refine ⟨heval, ?_⟩
  rw [heval]
  apply mul_ne_zero
  · exact pow_ne_zero ell (norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero))
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (sumSquares_pos q z (hno z hz)))

#print axioms effective_factor_polynomial
#assert_trust kernel effective_factor_polynomial

end
end NLA.IE02

/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Jordan
import NLA.SP05.Cone

noncomputable section
open Matrix
open scoped BigOperators Matrix MatrixOrder
namespace NLA.SP05

/-- The full real PSD global Jordan minimizer, including singular matrices and repeated spectra. -/
theorem global_positive_minimizer (n : ℕ) (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ μ : ℝ, ∃ X : Mat n, 0 < μ ∧ X.PosSemidef ∧ X ≠ 0 ∧
      jordanMatrix A B *ᵥ columnVec X = μ • columnVec X ∧
      ∀ v : Vec n, v ≠ 0 → μ ≤ rayleigh (jordanMatrix A B) v := by
  obtain ⟨r, W, hr, hW, hsign, heig, hS⟩ := jordan_inverse_top_sign n hn hA hB
  obtain ⟨hX, hX0, _, hquad⟩ := modulus_quadratic_improves (jordanMatrix A B)⁻¹
    (actual_jordan_inverse_cone hA hB) W hW hsign r heig
  have hJ := jordan_posDef hA hB
  have he := psd_slack_eigenvector hS hquad
  refine ⟨r⁻¹, CFC.abs W, inv_pos.mpr hr, hX, hX0, inverse_eigen_to_eigen hJ hr he, ?_⟩
  intro v hv
  exact rayleigh_lower_of_slack (inverse_slack_lower hJ hr hS) hv

#assert_trust kernel global_positive_minimizer
#print axioms global_positive_minimizer

end NLA.SP05

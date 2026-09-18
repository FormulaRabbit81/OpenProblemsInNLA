/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's natural-number induction and the proved finite Schur steps.

The dimension decreases at every strict step. The actual dimension-one
operator norm supplies the terminal scalar endpoint, with all SchurPair clauses.
-/
import NLA.IE02.SchurBasicNorms
import NLA.IE02.SchurEndpoint
import NLA.IE02.SchurPairStep

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem finite_schur_boundary {n : ℕ} (hn : 1 ≤ n) (U : Square n)
    (hU : IsToeplitz U) (hnorm : operatorNorm U = 1) :
    ∃ (d : ℕ) (a b : Poly), SchurPair n U d a b := by
  have hall : ∀ m : ℕ, 1 ≤ m → ∀ V : Square m,
      IsToeplitz V → operatorNorm V = 1 →
      ∃ (d : ℕ) (a b : Poly), SchurPair m V d a b := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm V hV hnormV
      rcases hV with ⟨p, rfl⟩
      cases m with
      | zero => omega
      | succ m =>
        cases m with
        | zero =>
          have hc : ‖p.coeff 0‖ = 1 := (schur_dimension_one p).symm.trans hnormV
          exact ⟨0, Polynomial.C (p.coeff 0), 1,
            (schur_scalar_endpoint (by omega) p hnormV hc).2⟩
        | succ m =>
          have hcle : ‖p.coeff 0‖ ≤ 1 := schur_diagonal_bound hm p hnormV.le
          by_cases hc : ‖p.coeff 0‖ = 1
          · exact ⟨0, Polynomial.C (p.coeff 0), 1,
              (schur_scalar_endpoint hm p hnormV hc).2⟩
          · have hclt : ‖p.coeff 0‖ < 1 := lt_of_le_of_ne hcle hc
            obtain ⟨B, _hB, hleft, hright, hZ, hdiag, hZnorm, hVnorm,
              _henergy, _htransport⟩ := schur_strict_reduction p hnormV hclt
            let Z := schurZ (toeplitz (m + 2) p) (p.coeff 0) B
            have hsmall : IsToeplitz (activeBlock Z) :=
              (schur_active_block Z hZ hdiag hZnorm.le).1
            -- The recursive input is the actual smaller Toeplitz active block.
            obtain ⟨d, a, b, hpair⟩ :=
              ih (m + 1) (by omega) (by omega) (activeBlock Z) hsmall hVnorm
            exact ⟨d + 1, schurNumerator (p.coeff 0) a b,
              schurDenominator (p.coeff 0) a b,
              schur_pair_step p a b B hnormV hclt hleft hright hVnorm hpair⟩
  exact hall n hn U hU hnorm

#print axioms finite_schur_boundary
#assert_trust kernel finite_schur_boundary

end
end NLA.IE02

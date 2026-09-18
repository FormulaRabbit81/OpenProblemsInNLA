/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

The complete original complex rank target. The upper bound uses the full
stable generalized eigenspace, and the lower bound uses nonzero pairings at
simple unit roots. No positivity of the limiting imaginary part, invertibility
of C or D, or semisimplicity of the interior spectrum is assumed.
-/
import NLA.MF18.SelectedCount
import NLA.MF18.SteinIdentity
import NLA.MF18.SimpleUnitPairing
import NLA.MF18.StableKernel
import NLA.MF18.SteinRankLower
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section
namespace NLA.MF18

theorem matrix_rank_nullity {n : ℕ} (H : Mat n) :
    H.rank + Module.finrank ℂ (LinearMap.ker H.toLin') = n := by
  -- Rewrite in the target so rank and kernel use the same mulVecLin
  -- instance, rather than independently elaborating a second finrank expression.
  rw [Matrix.rank, Matrix.toLin'_apply', LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_pi, Fintype.card_fin]

/-- Stronger than the canonical statement: uniqueness of the family is unused. -/
theorem full_complex_rank {n : ℕ} [NeZero n] (C D R P : Mat n)
    (X : ℝ → Mat n) (X₀ : Mat n) (m : ℕ)
    (h : GreenAssumptions C D R P X X₀)
    (hcount : circleRootCount (unregularizedPolynomial C R) = 2 * m) :
    (hermitianImaginaryPart X₀).rank = m := by
  have hlim := limiting_equation_and_spectra C D R P X X₀ h
  have hselected := selected_spectrum_count C D R P X X₀ m h hcount
  rcases h with ⟨hR, _hP, _hpos, _hstab, _hXlim, hXdet, _hreg, hsimple⟩
  have hstein := (stein_identity C R X₀ hR hXdet hlim.1).2
  have hfactor := unregularized_polynomial_factorization C R X₀ hXdet hlim.1
  have hnonzero : ∀ lam : ℂ, ‖lam‖ = 1 → ∀ v : Vec n, v ≠ 0 →
      (X₀⁻¹ * C).mulVec v = lam • v →
        pairing (hermitianImaginaryPart X₀) v v ≠ 0 := by
    intro lam hlam v hv heig
    have hroot := isRoot_charpoly_of_mulVec (X₀⁻¹ * C) lam v hv heig
    have hp : (unregularizedPolynomial C R).IsRoot lam := by
      -- Expose IsRoot as evaluation at lam being zero, so the polynomial factorization rewrites it.
      change (unregularizedPolynomial C R).eval lam = 0
      rw [hfactor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
        hroot, mul_zero, mul_zero]
    exact simple_unit_root_pairing C R X₀ hR hXdet hlim.1 lam hlam
      (hsimple lam hlam hp) v hv heig
  have hlower := stein_rank_lower_bound (X₀⁻¹ * C) (hermitianImaginaryPart X₀)
    hstein hselected.2.2 hnonzero
  rw [hselected.2.1] at hlower
  have hkernel := stable_space_in_kernel (X₀⁻¹ * C) (hermitianImaginaryPart X₀)
    hlim.2.1 hstein
  -- Fix the kernel finrank expression to the same explicit type as the
  -- rank-nullity helper before applying monotonicity to the stable subspace.
  have hkerdim : diskRootCount (X₀⁻¹ * C).charpoly ≤
      Module.finrank ℂ (LinearMap.ker (hermitianImaginaryPart X₀).toLin') := by
    rw [← stable_space_dimension]
    exact Submodule.finrank_mono hkernel
  have hnull := matrix_rank_nullity (hermitianImaginaryPart X₀)
  omega

theorem canonical_full_complex_rank {n : ℕ} [NeZero n] (C D R P : Mat n)
    (X : ℝ → Mat n) (X₀ : Mat n) (m : ℕ)
    (h : GreenAssumptions C D R P X X₀)
    (hunique : ∀ η : ℝ, 0 < η → ∀ Y : Mat n,
      IsStabilizingSolution C D R P η Y → Y = X η)
    (hcount : circleRootCount (unregularizedPolynomial C R) = 2 * m) :
    (hermitianImaginaryPart X₀).rank = m := by
  exact full_complex_rank C D R P X X₀ m h hcount

#print axioms full_complex_rank
#print axioms canonical_full_complex_rank

end NLA.MF18

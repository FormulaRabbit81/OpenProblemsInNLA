/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.

Mathlib's real Hahn–Banach separation is applied to the actual compact convex
gradient image. The already proved complex-coordinate representation gives
the exact descent direction with the correct second-slot inner convention.
-/
import NLA.IE02.GradientConvexity
import NLA.IE02.RealSeparator
import Mathlib.Analysis.LocallyConvex.Separation

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem gradient_strict_separation {n k : ℕ} (hn : 1 ≤ n)
    (T : Square n) (R : Fin k → Square n) (hT : IsToeplitz T) (hne : T ≠ 0)
    (hR : ∀ j, IsToeplitz (R j)) (hzero : 0 ∉ gradientImage T R) :
    ∃ (c : Fin k → ℂ) (γ : ℝ), 0 < γ ∧
      ∀ x ∈ unitMaximal T, γ ≤ descentForm T (directionSum R c) x := by
  obtain ⟨_hneimage, hc, hconv⟩ := gradient_compact_convex hn T R hT hne hR
  obtain ⟨ell, γ, hγ, hsep⟩ :=
    geometric_hahn_banach_point_closed hconv hc.isClosed hzero
  refine ⟨separatorCoefficients ell, γ, by simpa using hγ, ?_⟩
  intro x hx
  have haction : euclideanLin (directionSum R (separatorCoefficients ell)) x =
      ∑ j, separatorCoefficients ell j • euclideanLin (R j) x := by
    simp only [directionSum, euclideanLin, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply]
  have hform : ell (gradient T R x) =
      descentForm T (directionSum R (separatorCoefficients ell)) x := by
    rw [real_separator_complex_form ell]
    unfold descentForm
    rw [haction, inner_sum]
    simp only [inner_smul_right]
    rfl
  rw [← hform]
  exact (hsep (gradient T R x) ⟨x, hx, rfl⟩).le

#print axioms gradient_strict_separation
#assert_trust kernel gradient_strict_separation

end
end NLA.IE02

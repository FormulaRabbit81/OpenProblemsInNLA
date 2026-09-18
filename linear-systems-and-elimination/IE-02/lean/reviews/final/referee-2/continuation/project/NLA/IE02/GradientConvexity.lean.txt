/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.

Two-point weighted preservation proves convexity of the actual gradient image;
no closure or convex hull replaces that image. Compactness is independent.
-/
import NLA.IE02.MaximalPreservation
import NLA.IE02.GradientTopology
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem gradient_compact_convex {n k : ℕ} (hn : 1 ≤ n)
    (T : Square n) (R : Fin k → Square n) (hT : IsToeplitz T) (hne : T ≠ 0)
    (hR : ∀ j, IsToeplitz (R j)) :
    (gradientImage T R).Nonempty ∧ IsCompact (gradientImage T R) ∧
      Convex ℝ (gradientImage T R) := by
  have hc := gradient_nonempty_compact hn T R
  refine ⟨hc.1, hc.2, ?_⟩
  intro u hu v hv α β hα hβ hsum
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨y, hy, rfl⟩
  let f : Fin 2 → H n := ![x, y]
  let w : Fin 2 → ℝ := ![α, β]
  have hf : ∀ j, f j ∈ unitMaximal T := by
    intro j
    fin_cases j
    · exact hx
    · exact hy
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    fin_cases j
    · exact hα
    · exact hβ
  have hwsum : ∑ j, w j = 1 := by
    simpa [Fin.sum_univ_two, w] using hsum
  obtain ⟨z, hz, hgrad⟩ := maximal_complex_preservation hn T R hT hne hR f w hf hw hwsum
  refine ⟨z, hz, ?_⟩
  ext i
  -- The frozen WithLp coordinates and real scalar action reduce to the actual complex entries.
  change inner ℂ (euclideanLin T z) (euclideanLin (R i) z) =
    α • inner ℂ (euclideanLin T x) (euclideanLin (R i) x) +
    β • inner ℂ (euclideanLin T y) (euclideanLin (R i) y)
  simpa [Fin.sum_univ_two, f, w, Complex.real_smul] using hgrad i

#print axioms gradient_compact_convex
#assert_trust kernel gradient_compact_convex

end
end NLA.IE02

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.

A separated nonzero gradient would give the actual strict norm decrease
already proved by the descent estimates, contradicting the supplied global minimum.
-/
import NLA.IE02.GradientSeparation
import NLA.IE02.DescentConclusions

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem minimizer_orthogonality {n k : ℕ} (hn : 1 ≤ n)
    (T : Square n) (R : Fin k → Square n) (hT : IsToeplitz T) (hne : T ≠ 0)
    (hR : ∀ j, IsToeplitz (R j))
    (hmin : ∀ c : Fin k → ℂ, operatorNorm T ≤ operatorNorm (T + directionSum R c)) :
    ∃ x : H n, x ∈ unitMaximal T ∧
      ∀ j, inner ℂ (euclideanLin T x) (euclideanLin (R j) x) = 0 := by
  classical
  by_cases hzero : 0 ∈ gradientImage T R
  · obtain ⟨x, hx, hgrad⟩ := hzero
    refine ⟨x, hx, ?_⟩
    intro j
    exact congrArg (fun v : H k => v j) hgrad
  · obtain ⟨c, γ, hγ, hpos⟩ := gradient_strict_separation hn T R hT hne hR hzero
    obtain ⟨ε, _hε, hdecrease⟩ := positive_gradient_descent hn T (directionSum R c) hne γ hγ hpos
    have hdir : directionSum R (fun j => -(ε : ℂ) * c j) =
        -(ε : ℂ) • directionSum R c := by
      simp only [directionSum, Finset.smul_sum, smul_smul]
    have hbound := hmin (fun j => -(ε : ℂ) * c j)
    rw [hdir, neg_smul, ← sub_eq_add_neg] at hbound
    exact (not_lt_of_ge hbound hdecrease).elim

#print axioms minimizer_orthogonality
#assert_trust kernel minimizer_orthogonality

end
end NLA.IE02

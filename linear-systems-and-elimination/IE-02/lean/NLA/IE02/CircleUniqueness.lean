/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 attribution is retained in
Definitions.lean and SourceCorrespondence.md. Reuses Mathlib's polynomial
infinite-root criterion, interval infinitude and exact complex semicircle lemma.
-/
import NLA.IE02.Definitions
import Mathlib.Order.Interval.Set.Infinite
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem circle_polynomial_uniqueness (p q : Poly) :
    Set.Infinite {z : ℂ | ‖z‖ = 1} ∧
    ((∀ z : ℂ, ‖z‖ = 1 → p.eval z = q.eval z) → p = q) := by
  let f : ℝ → ℂ := fun t => (t : ℂ) + Complex.I * (Real.sqrt (1 - t ^ 2) : ℂ)
  have hreal (t : ℝ) : (f t).re = t := by simp [f]
  have hinj : Set.InjOn f (Set.Icc (-1 : ℝ) 1) := by
    intro a _ha b _hb hab
    simpa only [hreal] using congrArg Complex.re hab
  have hmap : Set.MapsTo f (Set.Icc (-1 : ℝ) 1) {z : ℂ | ‖z‖ = 1} := by
    intro t ht
    -- Unfold membership in the unit circle to its defining norm equality.
    change ‖f t‖ = 1
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm, one_pow]
    exact Complex.normSq_ofReal_add_I_mul_sqrt_one_sub
      (by simpa only [Real.norm_eq_abs] using (abs_le.mpr ht))
  have hinfinite : Set.Infinite {z : ℂ | ‖z‖ = 1} :=
    Set.infinite_of_injOn_mapsTo hinj hmap (Set.Icc_infinite (by norm_num))
  refine ⟨hinfinite, ?_⟩
  intro heq
  exact Polynomial.eq_of_infinite_eval_eq p q
    (hinfinite.mono (fun z hz => heq z hz))

#print axioms circle_polynomial_uniqueness
#assert_trust kernel circle_polynomial_uniqueness

end
end NLA.IE02

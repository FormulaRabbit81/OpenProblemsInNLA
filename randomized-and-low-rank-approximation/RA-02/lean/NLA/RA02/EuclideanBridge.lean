/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The actual complex quadratic form and squared Euclidean norm. The raw
function-space norm is never substituted for the Euclidean norm.
-/
import NLA.RA02.Definitions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma euclidean_toLp_ne_zero {n : ℕ} (x : Fin n → ℂ) (hx : x ≠ 0) :
    (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) ≠ 0 := by
  intro h
  exact hx ((WithLp.toLp_eq_zero 2).mp h)

lemma euclidean_norm_sq {n : ℕ} (x : Fin n → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ ^ 2 = squaredNorm x := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i : Fin n, ‖x i‖ ^ 2) = ∑ i : Fin n, Complex.normSq (x i)
  simp only [Complex.sq_norm]

lemma euclidean_quadratic {n : ℕ} (A : Square n) (x : Fin n → ℂ) :
    (inner ℂ (Matrix.toEuclideanLin A (WithLp.toLp 2 x))
      (WithLp.toLp 2 x)).re = quadraticValue A x := by
  change RCLike.re (inner ℂ (WithLp.toLp 2 (A *ᵥ x)) (WithLp.toLp 2 x)) =
    quadraticValue A x
  rw [inner_re_symm (𝕜 := ℂ)]
  change ((A *ᵥ x) ⬝ᵥ star x).re = (star x ⬝ᵥ (A *ᵥ x)).re
  rw [dotProduct_comm]

#print axioms euclidean_norm_sq
#assert_trust kernel euclidean_norm_sq
#print axioms euclidean_quadratic
#assert_trust kernel euclidean_quadratic

end
end NLA.RA02

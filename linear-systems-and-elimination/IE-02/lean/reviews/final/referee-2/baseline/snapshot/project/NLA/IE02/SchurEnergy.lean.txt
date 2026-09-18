/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's Euclidean matrix equivalence and adjoint/inner-product identities.

The matrix defect is evaluated in the actual complex Euclidean inner product.
No matrix supremum norm or positivity oracle enters this bridge.
-/
import NLA.IE02.SchurDefect

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem euclideanLin_one_apply {n : ℕ} (x : H n) : euclideanLin (1 : Square n) x = x := by
  -- Expose the frozen map as the existing exponent-two matrix equivalence.
  change Matrix.toLpLin 2 2 (1 : Square n) x = x
  rw [Matrix.toLpLin_one]
  rfl

theorem euclideanLin_mul_apply {n : ℕ} (A B : Square n) (x : H n) :
    euclideanLin (A * B) x = euclideanLin A (euclideanLin B x) := by
  -- The same Euclidean matrix equivalence sends multiplication to composition.
  change Matrix.toLpLin 2 2 (A * B) x =
    Matrix.toLpLin 2 2 A (Matrix.toLpLin 2 2 B x)
  rw [Matrix.toLpLin_mul_same]
  rfl

theorem euclideanLin_sub_apply {n : ℕ} (A B : Square n) (x : H n) :
    euclideanLin (A - B) x = euclideanLin A x - euclideanLin B x := by
  -- Unfold only the matrix-map wrapper to use its linearity.
  change Matrix.toLpLin 2 2 (A - B) x =
    Matrix.toLpLin 2 2 A x - Matrix.toLpLin 2 2 B x
  rw [map_sub]
  rfl

theorem euclideanLin_smul_apply {n : ℕ} (c : ℂ) (A : Square n) (x : H n) :
    euclideanLin (c • A) x = c • euclideanLin A x := by
  -- Unfold only the matrix-map wrapper to use its complex linearity.
  change Matrix.toLpLin 2 2 (c • A) x = c • Matrix.toLpLin 2 2 A x
  rw [map_smul]
  rfl

theorem euclidean_gram_energy {n : ℕ} (A : Square n) (x : H n) :
    (inner ℂ (euclideanLin (A.conjTranspose * A) x) x).re =
      ‖euclideanLin A x‖ ^ 2 := by
  rw [euclideanLin_mul_apply]
  -- Expose the conjugate-transpose map for the pinned Euclidean adjoint theorem.
  change (inner ℂ (Matrix.toEuclideanLin A.conjTranspose (euclideanLin A x)) x).re = _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (euclideanLin A x)).symm

theorem schur_energy_identity {n : ℕ} (U : Square n) (c : ℂ) (x : H n) :
    ‖euclideanLin (schurM U c) x‖ ^ 2 - ‖euclideanLin (U - c • 1) x‖ ^ 2 =
      (1 - ‖c‖ ^ 2) * (‖x‖ ^ 2 - ‖euclideanLin U x‖ ^ 2) := by
  have h := congrArg (fun A : Square n => (inner ℂ (euclideanLin A x) x).re)
    (schur_defect_identity U c)
  have hself : (inner ℂ x x).re = ‖x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [euclideanLin_sub_apply, euclideanLin_smul_apply,
    euclideanLin_one_apply, inner_sub_left, inner_smul_left,
    Complex.conj_ofReal, Complex.re_ofReal_mul, Complex.sub_re,
    euclidean_gram_energy, hself] using h

#print axioms schur_energy_identity
#assert_trust kernel schur_energy_identity

end
end NLA.IE02

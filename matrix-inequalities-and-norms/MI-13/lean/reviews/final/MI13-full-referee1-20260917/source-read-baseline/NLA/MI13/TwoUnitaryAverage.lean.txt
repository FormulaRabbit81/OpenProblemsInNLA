/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; prior mathematical attribution retained.

An actual square contraction is the average of two unitaries. The SVD reduces
the construction to the already proved symbolic unit-circle lift on [0,1].
-/
import NLA.MI13.SVD
import NLA.MI13.OperatorNorm
import NLA.MI13.ElementaryBounds

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

theorem isUnitary_conjTranspose {r : ℕ} {U : Square r} (hU : IsUnitary U) :
    IsUnitary U.conjTranspose := by
  simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1

theorem isUnitary_mul {r : ℕ} {U V : Square r} (hU : IsUnitary U)
    (hV : IsUnitary V) : IsUnitary (U * V) := by
  constructor
  · calc
      (U * V).conjTranspose * (U * V) =
          V.conjTranspose * (U.conjTranspose * U) * V := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = 1 := by rw [hU.1, Matrix.mul_one, hV.1]
  · calc
      (U * V) * (U * V).conjTranspose =
          U * (V * V.conjTranspose) * U.conjTranspose := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = 1 := by rw [hV.2, Matrix.mul_one, hU.2]

theorem isUnitary_diagonal {r : ℕ} (d : Fin r → ℂ)
    (hd : ∀ i, Complex.normSq (d i) = 1) : IsUnitary (Matrix.diagonal d) := by
  constructor
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    simpa only [Pi.star_apply, Complex.star_def, hd i, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := d i)).symm
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    simpa only [Pi.star_apply, Complex.star_def, hd i, Complex.ofReal_one] using
      Complex.mul_conj (d i)

theorem two_unitary_average {r : ℕ} (B : Square r) (hB : spectralNorm B ≤ 1) :
    ∃ U V : Square r, IsUnitary U ∧ IsUnitary V ∧ B = (1 / 2 : ℂ) • (U + V) := by
  classical
  obtain ⟨U, V, hU, hV, hsvd⟩ := full_svd B
  have hs := singular_values_semantics B
  have hsmall (i : Fin r) : singularValue B i.val ≤ 1 :=
    (hs.2.1 (Nat.zero_le i.val)).trans ((operator_norm_semantics B).1 ▸ hB)
  let dp : Fin r → ℂ := fun i => circlePlus (singularValue B i.val)
  let dm : Fin r → ℂ := fun i => circleMinus (singularValue B i.val)
  have hlift (i : Fin r) := unit_circle_lift (singularValue B i.val)
    (hs.1 i.val) (hsmall i)
  have hdp : IsUnitary (Matrix.diagonal dp) :=
    isUnitary_diagonal dp (fun i => (hlift i).1)
  have hdm : IsUnitary (Matrix.diagonal dm) :=
    isUnitary_diagonal dm (fun i => (hlift i).2.1)
  -- Diagonal averaging is entrywise; no grid or approximate computation
  -- replaces the exact scalar identity, including zero singular values.
  have hdiag : singularDiagonal B =
      (1 / 2 : ℂ) • (Matrix.diagonal dp + Matrix.diagonal dm) := by
    rw [Matrix.diagonal_add, ← Matrix.diagonal_smul]
    apply congrArg Matrix.diagonal
    funext i
    exact (hlift i).2.2.symm
  refine ⟨U * Matrix.diagonal dp * V.conjTranspose,
    U * Matrix.diagonal dm * V.conjTranspose,
    isUnitary_mul (isUnitary_mul hU hdp) (isUnitary_conjTranspose hV),
    isUnitary_mul (isUnitary_mul hU hdm) (isUnitary_conjTranspose hV), ?_⟩
  -- Transport the scalar average through the fixed left and right SVD factors.
  rw [hsvd, hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

#print axioms two_unitary_average
#assert_trust kernel two_unitary_average

end
end NLA.MI13

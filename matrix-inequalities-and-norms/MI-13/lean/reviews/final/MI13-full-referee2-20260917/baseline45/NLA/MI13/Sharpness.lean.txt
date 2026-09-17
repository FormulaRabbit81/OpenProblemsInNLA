/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; prior mathematical attribution retained.

The two-by-two equality example uses exact finite algebra. Its singular values
come from the genuine identity Gram operator, without numerical eigenvalue bounds.
-/
import NLA.MI13.TwoUnitaryAverage

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

theorem unitary_singularValue_sq {r : ℕ} (U : Square r) (hU : IsUnitary U) (i : Fin r) :
    singularValue U i.val ^ 2 = 1 := by
  have hgram : (euclideanLin U).adjoint ∘ₗ euclideanLin U = LinearMap.id := by
    rw [euclideanLin, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toLpLin_mul 2 2 2, hU.1, Matrix.toLpLin_one]
  obtain ⟨v, hv⟩ := ordered_gram_basis U
  have h := hv i
  -- The composed Gram map has the same action as the nested application
  -- in GramBasis; exposing that composition permits the identity rewrite.
  change ((euclideanLin U).adjoint ∘ₗ euclideanLin U) (v i) =
    (singularValue U i.val : ℂ) ^ 2 • v i at h
  rw [hgram, LinearMap.id_apply] at h
  have hne : v i ≠ 0 := by
    intro hz
    have hn := v.norm_eq_one i
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hscalar : (1 : ℂ) = (singularValue U i.val : ℂ) ^ 2 :=
    smul_left_injective ℂ hne (by simpa only [one_smul] using h)
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_pow, Complex.ofReal_one] using hscalar.symm

theorem sharpness_example :
    frobeniusNorm (sharpA * (1 : Square 2) * sharpC - sharpC * (1 : Square 2) * sharpA) ^ 2 = 4 ∧
    spectralNorm (1 : Square 2) ^ 2 = 1 ∧ singularValue sharpA 0 ^ 2 = 1 ∧
    singularValue sharpA 1 ^ 2 = 1 ∧ frobeniusNorm sharpC ^ 2 = 1 := by
  have hI : IsUnitary (1 : Square 2) := by simp [IsUnitary]
  have hA : IsUnitary sharpA := by
    apply isUnitary_diagonal
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  refine ⟨?_, ?_, unitary_singularValue_sq sharpA hA 0,
    unitary_singularValue_sq sharpA hA 1, ?_⟩
  · rw [(frobenius_semantics _).1]
    norm_num [sharpA, sharpC, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [(operator_norm_semantics (1 : Square 2)).1]
    exact unitary_singularValue_sq 1 hI 0
  · rw [(frobenius_semantics sharpC).1]
    norm_num [sharpC, Fin.sum_univ_two]

#print axioms sharpness_example
#assert_trust kernel sharpness_example

end
end NLA.MI13

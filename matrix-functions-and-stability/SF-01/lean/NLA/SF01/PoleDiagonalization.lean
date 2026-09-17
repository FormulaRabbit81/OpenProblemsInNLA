/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Actual real orthogonal diagonalization, using Mathlib's opaque matrix-level
spectral theorem. No eigenvalue ordering or simple-spectrum assumption is used.
-/
import NLA.SF01.PoleEnergy
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma orthogonal_of_unitary_real {n : ℕ}
    (Q : Matrix.unitaryGroup (Fin n) ℝ) : IsOrthogonal (Q : Square n) := by
  constructor
  · simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self Q
  · simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self Q

theorem pole_diagonalization_exists (d : RidgeData) (hd : ValidData d) :
    ∃ Q : Square (d.size + 1), ∃ lam : Fin (d.size + 1) → ℝ,
      PoleDiagonalization d Q lam := by
  let hp : (poleMatrix d).PosDef := pole_positive_definite d hd
  let hH : (poleMatrix d).IsHermitian := hp.isHermitian
  refine ⟨(hH.eigenvectorUnitary : Square (d.size + 1)), hH.eigenvalues,
    orthogonal_of_unitary_real hH.eigenvectorUnitary, ?_, ?_⟩
  · intro i
    exact hp.eigenvalues_pos i
  · simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hH.spectral_theorem

lemma orthogonal_transpose_dot {n : ℕ} (Q : Square n) (hQ : IsOrthogonal Q)
    (x y : Vector n) :
    (Q.transpose *ᵥ x) ⬝ᵥ (Q.transpose *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hQ.2,
    Matrix.one_mulVec, dotProduct_comm]

end
end NLA.SF01

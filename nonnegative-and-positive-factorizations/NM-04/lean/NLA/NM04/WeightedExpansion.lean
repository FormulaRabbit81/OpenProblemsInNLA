/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain authorship of the
coefficient question; Matthew J. Colbrook retains authorship of its solution.

The weighted principal-minor expansion, including zero weights and empty indices.
-/
import NLA.NM04.Definitions
import LeanCert.Tactic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators Matrix
universe u w

/-- Expand in rows, factor their weights, then retain the chosen principal minor. -/
private theorem diagonal_add_row_weights {D : Type u} [Fintype D] [DecidableEq D]
    {𝕜 : Type w} [CommRing 𝕜] (N : Matrix D D 𝕜) (c γ : D → 𝕜) :
    (Matrix.diagonal γ + Matrix.of (fun i j => c i * N i j)).det =
      ∑ E : Finset D,
        (N.submatrix (Subtype.val : E → D) (Subtype.val : E → D)).det *
          (∏ i ∈ E, c i) * (∏ i ∈ (Finset.univ \ E), γ i) := by
  let F : (D → 𝕜) [⋀^D]→ₗ[𝕜] 𝕜 := Matrix.detRowAlternating
  have hdiag : Matrix.diagonal γ =
      Matrix.of (fun i j => γ i * (1 : Matrix D D 𝕜) i j) := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij]
  calc
    _ = F ((fun i => c i • N i) + (fun i => γ i • (1 : Matrix D D 𝕜) i)) := by
      rw [hdiag]
      -- Expose the determinant under its alternating-map wrapper.
      change Matrix.det _ = Matrix.det _
      congr 1
      ext i j
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm]
    _ = ∑ E : Finset D,
        F (E.piecewise (fun i => c i • N i)
          (fun i => γ i • (1 : Matrix D D 𝕜) i)) := F.map_add_univ _ _
    _ = ∑ E : Finset D,
        (∏ i, if i ∈ E then c i else γ i) *
          F (E.piecewise N (1 : Matrix D D 𝕜)) := by
      apply Finset.sum_congr rfl
      intro E _
      have hrows : E.piecewise (fun i => c i • N i)
          (fun i => γ i • (1 : Matrix D D 𝕜) i) =
          fun i => (if i ∈ E then c i else γ i) •
            E.piecewise N (1 : Matrix D D 𝕜) i := by
        funext i
        by_cases hi : i ∈ E <;> simp [Finset.piecewise, hi]
      rw [hrows, F.map_smul_univ, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E _
      -- Convert the piecewise row function to the matrix expected by the principal-minor API.
      change (∏ i, if i ∈ E then c i else γ i) *
        (Matrix.of (E.piecewise N.row (1 : Matrix D D 𝕜).row)).det = _
      rw [Matrix.det_piecewise_one_eq_submatrix_det, Finset.prod_ite,
        Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_notMem_eq_sdiff]
      ring

-- The public contract uses the frozen statement's decision-instance convention.
attribute [local instance] Classical.propDecidable

/-- Weighted principal minors with no nonzero-diagonal or nonempty-type assumptions. -/
theorem weighted_principal_minor_expansion {D : Type u} [Fintype D] [DecidableEq D]
    {𝕜 : Type w} [CommRing 𝕜] (M : Matrix D D 𝕜) (γ δ : D → 𝕜) (z : 𝕜) :
    (Matrix.diagonal γ + z • (M * Matrix.diagonal δ)).det =
      ∑ E : Finset D,
        (M.submatrix (Subtype.val : E → D) (Subtype.val : E → D)).det *
          (∏ i ∈ E, δ i) * (∏ i ∈ (Finset.univ \ E), γ i) * z ^ E.card := by
  let N : Matrix D D 𝕜 := M.transpose
  have ht : (Matrix.diagonal γ + z • (M * Matrix.diagonal δ)).transpose =
      Matrix.diagonal γ + Matrix.of (fun i j => (z * δ i) * N i j) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_diagonal, Matrix.of_apply, smul_eq_mul, N]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      ring
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
      ring
  calc
    _ = (Matrix.diagonal γ + z • (M * Matrix.diagonal δ)).transpose.det :=
      (Matrix.det_transpose _).symm
    _ = (Matrix.diagonal γ + Matrix.of (fun i j => (z * δ i) * N i j)).det :=
      congrArg Matrix.det ht
    _ = ∑ E : Finset D,
        (N.submatrix (Subtype.val : E → D) (Subtype.val : E → D)).det *
          (∏ i ∈ E, z * δ i) * (∏ i ∈ (Finset.univ \ E), γ i) :=
      diagonal_add_row_weights N (fun i => z * δ i) γ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E _
      have hminor :
          (N.submatrix (Subtype.val : E → D) (Subtype.val : E → D)).det =
          (M.submatrix (Subtype.val : E → D) (Subtype.val : E → D)).det := by
        -- Transpose commutes definitionally with this principal-submatrix restriction.
        change (M.submatrix (Subtype.val : E → D) (Subtype.val : E → D)).transpose.det = _
        exact Matrix.det_transpose _
      rw [hminor, Finset.prod_mul_distrib, Finset.prod_const]
      ring

#print axioms weighted_principal_minor_expansion
#assert_trust kernel weighted_principal_minor_expansion

end
end NLA.NM04

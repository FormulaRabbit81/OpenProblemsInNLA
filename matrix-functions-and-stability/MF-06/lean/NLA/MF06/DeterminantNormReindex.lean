/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Separately reordering a minor's rows and columns can change its sign. This
norm identity retains both actual equivalences, reduces their discrepancy to
one genuine permutation sign, and uses the norm-one integer-unit action. It
is not an unsigned determinant identity and requires no nonsingularity.
Mathlib's determinant reindexing and integer-unit norm lemmas are reused.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06

lemma norm_det_submatrix_equiv_equiv {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e₁ e₂ : ι ≃ κ) (A : Matrix κ κ ℂ) :
    ‖(A.submatrix e₁ e₂).det‖ = ‖A.det‖ := by
  have hee : e₂ = e₁.trans (e₁.symm.trans e₂) := by ext; simp
  rw [hee]
  change ‖((A.submatrix id (e₁.symm.trans e₂)).submatrix e₁ e₁).det‖ = ‖A.det‖
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute']
  simpa only [Units.smul_def, zsmul_eq_mul] using
    norm_units_zsmul (Equiv.Perm.sign (e₁.symm.trans e₂)) A.det

#print axioms norm_det_submatrix_equiv_equiv
#assert_trust kernel norm_det_submatrix_equiv_equiv

end NLA.MF06

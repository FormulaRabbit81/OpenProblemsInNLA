/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A nonzero literal minor has a Leibniz term with no zero entries. For an upper
block matrix its permutation matches each row label below the corresponding
column label. Equal total label weight forces equality of every matched label,
and therefore equality of every occupation count. No invertibility assumption
or enumeration of permutations is used.
-/
import NLA.MF06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

def minorLabelWeight {d r : ℕ} {ι : Type*} [Fintype ι]
    (b : Fin d → Fin r) (e : ι → Fin d) : ℕ :=
  ∑ j : ι, (b (e j)).val

def minorLabelCount {d r : ℕ} {ι : Type*} [Fintype ι]
    (b : Fin d → Fin r) (e : ι → Fin d) (i : Fin r) : ℕ :=
  Fintype.card {j : ι // b (e j) = i}

/-- The matching is extracted from the actual determinant formula. The row
and column maps need not be injective, so repeated-index zero minors are also
within the statement. -/
lemma minor_nonzero_matching {d r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Fin d → Fin r) (A : Square d)
    (hA : IsUpperBlockTriangular b A) (e f : ι → Fin d)
    (hne : Matrix.det (A.submatrix e f) ≠ 0) :
    ∃ σ : Equiv.Perm ι, ∀ j : ι, b (e (σ j)) ≤ b (f j) := by
  classical
  have hsum : (∑ σ : Equiv.Perm ι,
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j : ι, A (e (σ j)) (f j)) ≠ 0 := by
    simpa only [Matrix.det_apply', Matrix.submatrix_apply] using hne
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hprod : (∏ j : ι, A (e (σ j)) (f j)) ≠ 0 := (mul_ne_zero_iff.mp hσ).2
  refine ⟨σ, fun j => le_of_not_gt ?_⟩
  intro hj
  exact (Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j))
    (hA (e (σ j)) (f j) hj)

lemma minor_weight_le_of_nonzero {d r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Fin d → Fin r) (A : Square d)
    (hA : IsUpperBlockTriangular b A) (e f : ι → Fin d)
    (hne : Matrix.det (A.submatrix e f) ≠ 0) :
    minorLabelWeight b e ≤ minorLabelWeight b f := by
  obtain ⟨σ, hσ⟩ := minor_nonzero_matching b A hA e f hne
  calc
    minorLabelWeight b e = ∑ j : ι, (b (e (σ j))).val :=
      (Equiv.sum_comp σ (fun j : ι => (b (e j)).val)).symm
    _ ≤ minorLabelWeight b f :=
      Finset.sum_le_sum (fun j _ => Fin.le_def.mp (hσ j))

/-- Equality of the total weights turns every permitted inequality into an
equality. This also works for empty minors, whose matching is empty. -/
lemma minor_equal_weight_matching {d r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Fin d → Fin r) (A : Square d)
    (hA : IsUpperBlockTriangular b A) (e f : ι → Fin d)
    (hne : Matrix.det (A.submatrix e f) ≠ 0)
    (heq : minorLabelWeight b e = minorLabelWeight b f) :
    ∃ σ : Equiv.Perm ι, ∀ j : ι, b (e (σ j)) = b (f j) := by
  obtain ⟨σ, hσ⟩ := minor_nonzero_matching b A hA e f hne
  have hsum : (∑ j : ι, (b (e (σ j))).val) = ∑ j : ι, (b (f j)).val :=
    (Equiv.sum_comp σ (fun j : ι => (b (e j)).val)).trans heq
  have hpoint := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Fin.le_def.mp (hσ j))).mp hsum
  exact ⟨σ, fun j => Fin.ext (hpoint j (Finset.mem_univ j))⟩

lemma minor_counts_eq_of_matching {d r : ℕ} {ι : Type*} [Fintype ι]
    (b : Fin d → Fin r) (e f : ι → Fin d) (σ : Equiv.Perm ι)
    (hσ : ∀ j : ι, b (e (σ j)) = b (f j)) (i : Fin r) :
    minorLabelCount b e i = minorLabelCount b f i := by
  let E : {j : ι // b (e j) = i} ≃ {j : ι // b (f j) = i} :=
    { toFun := fun j => ⟨σ.symm j.val, by
        rw [← hσ (σ.symm j.val), σ.apply_symm_apply]
        exact j.property⟩
      invFun := fun j => ⟨σ j.val, (hσ j.val).trans j.property⟩
      left_inv := fun j => Subtype.ext (σ.apply_symm_apply j.val)
      right_inv := fun j => Subtype.ext (σ.symm_apply_apply j.val) }
  exact Fintype.card_congr E

lemma minor_counts_eq_of_nonzero_equal_weight {d r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Fin d → Fin r) (A : Square d)
    (hA : IsUpperBlockTriangular b A) (e f : ι → Fin d)
    (hne : Matrix.det (A.submatrix e f) ≠ 0)
    (heq : minorLabelWeight b e = minorLabelWeight b f) (i : Fin r) :
    minorLabelCount b e i = minorLabelCount b f i := by
  obtain ⟨σ, hσ⟩ := minor_equal_weight_matching b A hA e f hne heq
  exact minor_counts_eq_of_matching b e f σ hσ i

lemma minor_eq_zero_of_weight_lt {d r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Fin d → Fin r) (A : Square d)
    (hA : IsUpperBlockTriangular b A) (e f : ι → Fin d)
    (hlt : minorLabelWeight b f < minorLabelWeight b e) :
    Matrix.det (A.submatrix e f) = 0 := by
  by_contra hne
  exact (not_le_of_gt hlt) (minor_weight_le_of_nonzero b A hA e f hne)

#print axioms minor_nonzero_matching
#assert_trust kernel minor_nonzero_matching
#print axioms minor_counts_eq_of_nonzero_equal_weight
#assert_trust kernel minor_counts_eq_of_nonzero_equal_weight
#print axioms minor_eq_zero_of_weight_lt
#assert_trust kernel minor_eq_zero_of_weight_lt

end NLA.MF06

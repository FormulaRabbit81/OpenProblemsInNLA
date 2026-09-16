import NLA.KE05.Regular

/- Closure for actual matrix operations, including determinant, adjugate and
nonsingular inverse. No determinant is treated as an independent scalar oracle. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.KE05

lemma regular_matrix_det {σ : Type*} {a : σ → ℝ} {b : ℕ}
    (A : (σ → ℝ) → Mat b) (hA : ∀ i j, RegularAt a (fun x => A x i j)) :
    RegularAt a (fun x => (A x).det) := by
  simp_rw [Matrix.det_apply']
  apply RegularAt.sum
  intro p hp
  apply RegularAt.mul
  · exact RegularAt.const _
  · apply RegularAt.prod
    intro i hi
    exact hA (p i) i

lemma regular_matrix_adjugate {σ : Type*} {a : σ → ℝ} {b : ℕ}
    (A : (σ → ℝ) → Mat b) (hA : ∀ i j, RegularAt a (fun x => A x i j)) (i j : Fin b) :
    RegularAt a (fun x => (A x).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply regular_matrix_det
  intro r c
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact RegularAt.const _
  · simp only [Matrix.updateRow_ne hr]
    exact hA r c

lemma regular_matrix_inv {σ : Type*} {a : σ → ℝ} {b : ℕ}
    (A : (σ → ℝ) → Mat b) (hA : ∀ i j, RegularAt a (fun x => A x i j))
    (ha : (A a).det ≠ 0) (i j : Fin b) : RegularAt a (fun x => (A x)⁻¹ i j) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((regular_matrix_det A hA).inv ha).mul (regular_matrix_adjugate A hA i j)

lemma regular_matrix_mul {σ : Type*} {a : σ → ℝ} {b : ℕ}
    (A B : (σ → ℝ) → Mat b) (hA : ∀ i j, RegularAt a (fun x => A x i j))
    (hB : ∀ i j, RegularAt a (fun x => B x i j)) (i j : Fin b) :
    RegularAt a (fun x => (A x * B x) i j) := by
  simp_rw [Matrix.mul_apply]
  apply RegularAt.sum
  intro k hk
  exact (hA i k).mul (hB k j)

lemma regular_matrix_trace {σ : Type*} {a : σ → ℝ} {b : ℕ}
    (A : (σ → ℝ) → Mat b) (hA : ∀ i j, RegularAt a (fun x => A x i j)) :
    RegularAt a (fun x => (A x).trace) := by
  apply RegularAt.sum
  intro i hi
  exact hA i i

end NLA.KE05

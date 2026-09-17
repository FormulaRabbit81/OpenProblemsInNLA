import NLA.IV03.Proof
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NLA.IV03

lemma vertex_formula_proved {n : ℕ} (L U : Mat n) (s : ℝ) (i j : Fin n) :
    vertex L U s i j = center L U + s •
      (Matrix.diagonal (signVector i) * radius L U * Matrix.diagonal (signVector j)) := by
  ext k l
  simp [vertex, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

lemma vertex_minus_entry {n : ℕ} (L U : Mat n) (i j k l : Fin n) :
    vertex L U (-1) i j k l = if (k=i ↔ l=j) then L k l else U k l := by
  by_cases hk : k=i <;> by_cases hl : l=j <;>
    simp [vertex,signVector,center,radius,hk,hl] <;> ring

lemma vertices_admissible_proved {n : ℕ} (L U : Mat n) (h : OrderedEndpoints L U)
    (i j : Fin n) (s : ℝ) (hs : s ∈ ({(-1:ℝ),1} : Set ℝ)) :
    vertex L U s i j ∈ intervalFamily L U := by
  intro k l
  have hkl := h k l
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  all_goals by_cases hk : k=i <;> by_cases hl : l=j <;>
    simp_all [vertex,signVector,center,radius] <;> constructor <;> linarith

lemma lower_nonnegative_of_vertices {n : ℕ} (L U : Mat n)
    (h : ∀ i j, IsInverseM (vertex L U (-1) i j)) : ∀ k l, 0 ≤ L k l := by
  intro k l
  simpa [vertex_minus_entry] using (h k l).2.1 k l

lemma lower_diagonal_positive_of_vertices {n : ℕ} (L U : Mat n)
    (h : ∀ i j, IsInverseM (vertex L U (-1) i j)) : ∀ k, 0 < L k k := by
  intro k
  simpa [vertex_minus_entry] using (inverseM_diagonal_pos (h k k) k).1

lemma interval_inverseM_one (L U : Mat 1) (_h : OrderedEndpoints L U)
    (hv : ∀ i j, IsInverseM (vertex L U (-1) i j))
    (A : Mat 1) (hA : A ∈ intervalFamily L U) : IsInverseM A := by
  have hp : 0 < A 0 0 := lt_of_lt_of_le (lower_diagonal_positive_of_vertices L U hv 0) (hA 0 0).1
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).mpr ?_,?_,?_⟩
  · simpa [Matrix.det_fin_one] using (isUnit_iff_ne_zero.mpr hp.ne')
  · intro i j
    fin_cases i <;> fin_cases j
    exact hp.le
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

lemma inverseM_two_of_det_pos (A : Mat 2) (hA : ∀ i j, 0 ≤ A i j)
    (hd : 0 < A.det) : IsInverseM A := by
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hd.ne'),hA,?_⟩
  intro i j hij
  have hdet : 0 ≤ A.det⁻¹ := inv_nonneg.mpr hd.le
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa [Matrix.adjugate_fin_two] using mul_nonpos_of_nonneg_of_nonpos hdet (neg_nonpos.mpr (hA 0 1))
  · simpa [Matrix.adjugate_fin_two] using mul_nonpos_of_nonneg_of_nonpos hdet (neg_nonpos.mpr (hA 1 0))
  · exact (hij rfl).elim

lemma interval_inverseM_two (L U : Mat 2) (_h : OrderedEndpoints L U)
    (hv : ∀ i j, IsInverseM (vertex L U (-1) i j))
    (A : Mat 2) (hA : A ∈ intervalFamily L U) : IsInverseM A := by
  have hL := lower_nonnegative_of_vertices L U hv
  have hnn : ∀ i j, 0 ≤ A i j := fun i j => le_trans (hL i j) (hA i j).1
  have hc := inverseM_det_pos (hv 0 0)
  norm_num [Matrix.det_fin_two,vertex_minus_entry,Fin.ext_iff] at hc
  have hdiag : L 0 0 * L 1 1 ≤ A 0 0 * A 1 1 :=
    mul_le_mul (hA 0 0).1 (hA 1 1).1 (hL 1 1) (hnn 0 0)
  have hoff : A 0 1 * A 1 0 ≤ U 0 1 * U 1 0 :=
    mul_le_mul (hA 0 1).2 (hA 1 0).2 (hnn 1 0) (le_trans (hnn 0 1) (hA 0 1).2)
  apply inverseM_two_of_det_pos A hnn
  rw [Matrix.det_fin_two]
  linarith

end NLA.IV03

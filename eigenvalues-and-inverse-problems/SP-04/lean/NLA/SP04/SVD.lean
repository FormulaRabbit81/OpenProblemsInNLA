/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.SpectralIntervals
import NLA.SP04.Orthogonal
import NLA.SP04.MatrixStationary

noncomputable section
open scoped BigOperators Matrix
namespace NLA.SP04

lemma gram_isHermitian (U : Mat 3) : (Uᵀ * U).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Reorder the actual orthonormal Gram eigenbasis by an arbitrary bijection. -/
lemma reordered_gram_basis (U : Mat 3) (e : Fin 3 ≃ Fin 3) :
    ∃ Q : Mat 3, Orthogonal Q ∧
      Qᵀ * (Uᵀ * U) * Q = Matrix.diagonal (fun i => (gram_isHermitian U).eigenvalues (e i)) := by
  let hG := gram_isHermitian U
  let E : Mat 3 := hG.eigenvectorUnitary
  have hE : Orthogonal E := by
    constructor
    · simpa [E, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.coe_star_mul_self hG.eigenvectorUnitary
    · simpa [E, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using
        Unitary.coe_mul_star_self hG.eigenvectorUnitary
  have hd : Eᵀ * (Uᵀ * U) * E = Matrix.diagonal hG.eigenvalues := by
    simpa [Unitary.conjStarAlgAut_star_apply, E, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using
      hG.conjStarAlgAut_star_eigenvectorUnitary
  let Q : Mat 3 := E.submatrix id e
  have ht : Qᵀ = Eᵀ.submatrix e id := rfl
  have hQt : Qᵀ * Q = 1 := by
    rw [ht]
    change Eᵀ.submatrix e id * E.submatrix id e = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hE.1]
    exact Matrix.submatrix_one e e.injective
  refine ⟨Q, ⟨hQt, mul_eq_one_comm.mp hQt⟩, ?_⟩
  rw [ht]
  change Eᵀ.submatrix e id * (Uᵀ * U) * E.submatrix id e = _
  have heq : Eᵀ.submatrix e id * (Uᵀ * U) * E.submatrix id e =
      (Eᵀ * (Uᵀ * U) * E).submatrix e e := by
    rw [Matrix.submatrix_mul _ E e id e Function.bijective_id,
      Matrix.submatrix_mul Eᵀ _ e id id Function.bijective_id]
    rfl
  rw [heq, hd, Matrix.submatrix_diagonal_equiv]
  rfl

lemma root_is_gram_eigenvalue (U : Mat 3) {r : ℝ}
    (hr : (Uᵀ * U).charpoly.eval r = 0) :
    ∃ j : Fin 3, (gram_isHermitian U).eigenvalues j = r := by
  rw [(gram_isHermitian U).charpoly_eq, Polynomial.eval_prod] at hr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    RCLike.ofReal_real_eq_id, id_eq, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero] at hr
  exact hr.imp fun _ h => h.symm

lemma interval_sqrt_bounds (i : Fin 3) {r : ℝ}
    (hl : (lowerEndpoint i)^2 < r) (hu : r < (upperEndpoint i)^2) :
    lowerEndpoint i < Real.sqrt r ∧ Real.sqrt r < upperEndpoint i := by
  have hlo : 0 < lowerEndpoint i := by fin_cases i <;> norm_num [lowerEndpoint]
  have hup : 0 < upperEndpoint i := by fin_cases i <;> norm_num [upperEndpoint]
  have hr : 0 ≤ r := le_of_lt (lt_trans (sq_pos_of_pos hlo) hl)
  have hsq := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg r
  constructor <;> nlinarith

lemma interval_roots_admissible (r : Fin 3 → ℝ)
    (hl : ∀ i, (lowerEndpoint i)^2 < r i) (hu : ∀ i, r i < (upperEndpoint i)^2) :
    Admissible (fun i => Real.sqrt (r i)) := by
  have h0 := interval_sqrt_bounds 0 (hl 0) (hu 0)
  have h1 := interval_sqrt_bounds 1 (hl 1) (hu 1)
  have h2 := interval_sqrt_bounds 2 (hl 2) (hu 2)
  norm_num [lowerEndpoint, upperEndpoint, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail] at h0 h1 h2
  exact ⟨h0.1, by linarith, by linarith, h2.2⟩

/-- Normalize the Gram eigenvectors to obtain the second orthogonal factor. -/
lemma svd_of_gram_diagonal (U Q : Mat 3) (s : Fin 3 → ℝ)
    (hQ : Orthogonal Q) (hs : ∀ i, s i ≠ 0)
    (hg : Qᵀ * (Uᵀ * U) * Q = Matrix.diagonal (fun i => (s i)^2)) :
    HasSVD U s := by
  let D : Mat 3 := Matrix.diagonal (fun i => (s i)⁻¹)
  let P : Mat 3 := U * Q * D
  have hD : Dᵀ = D := Matrix.diagonal_transpose _
  have hPP : Pᵀ * P = 1 := by
    calc
      Pᵀ * P = D * (Qᵀ * (Uᵀ * U) * Q) * D := by
        simp only [P, Matrix.transpose_mul, hD, Matrix.mul_assoc]
      _ = D * Matrix.diagonal (fun i => (s i)^2) * D := by rw [hg]
      _ = 1 := by
        simp only [D, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases hij : i = j
        · subst j; simp [hs, pow_two]
        · simp [hij]
  have hDS : D * Matrix.diagonal s = 1 := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [hs]
    · simp [hij]
  refine ⟨P, Q, ⟨hPP, mul_eq_one_comm.mp hPP⟩, hQ, ?_⟩
  symm
  calc
    P * Matrix.diagonal s * Qᵀ = U * Q * (D * Matrix.diagonal s) * Qᵀ := by
      simp only [P, Matrix.mul_assoc]
    _ = U := by rw [hDS]; simp [Matrix.mul_assoc, hQ.2]

/-- Every matrix in the strict polynomial-sign family has a genuine admissible SVD. -/
lemma family_has_admissible_svd (U : Mat 3) (hU : U ∈ counterexampleFamily) :
    ∃ s : Fin 3 → ℝ, Admissible s ∧ HasSVD U s := by
  choose r hl hu hr using gram_root_in_interval U hU
  let s : Fin 3 → ℝ := fun i => Real.sqrt (r i)
  have hs : Admissible s := interval_roots_admissible r hl hu
  have hri : Function.Injective r := by
    intro i j hij
    apply admissible_injective hs
    exact congrArg Real.sqrt hij
  choose f hf using fun i => root_is_gram_eigenvalue U (hr i)
  have hfi : Function.Injective f := by
    intro i j hij
    apply hri
    rw [← hf i, ← hf j, hij]
  let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective f ⟨hfi, Finite.injective_iff_surjective.mp hfi⟩
  obtain ⟨Q, hQ, hg⟩ := reordered_gram_basis U e
  refine ⟨s, hs, svd_of_gram_diagonal U Q s hQ (fun i => ne_of_gt (admissible_pos hs i)) ?_⟩
  rw [hg]
  congr 1
  funext i
  change (gram_isHermitian U).eigenvalues (f i) = (Real.sqrt (r i))^2
  rw [hf i, Real.sq_sqrt (le_of_lt (lt_of_le_of_lt (sq_nonneg _) (hl i)))]

end NLA.SP04

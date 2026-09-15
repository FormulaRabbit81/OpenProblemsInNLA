/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.Geometry
import NLA.IE17.NumericData
import NLA.IE17.LSMR

noncomputable section
open Matrix
namespace NLA.IE17

/-- All four Penrose laws determine the projected vector, without choosing a total inverse. -/
lemma penrose_projection_unique {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {K : Matrix ι κ ℝ} {P Q : Matrix κ ι ℝ}
    (hP : IsMoorePenrose K P) (hQ : IsMoorePenrose K Q) : K * P = K * Q := by
  have hPQ : (K * P) * (K * Q) = K * Q := by
    rw [← Matrix.mul_assoc, hP.1]
  have hQP : (K * Q) * (K * P) = K * P := by
    rw [← Matrix.mul_assoc, hQ.1]
  have ht := congrArg Matrix.transpose hPQ
  simp only [Matrix.transpose_mul, hQ.2.2.1, hP.2.2.1] at ht
  exact hQP.symm.trans ht

lemma approximation_unique {m n : ℕ} {A : Mat m n} {b : Vec m} {x : Vec n}
    {p q : ℝ} (hp : IsApproximation A b x p) (hq : IsApproximation A b x q) : p = q := by
  unfold IsApproximation at hp hq
  by_cases hz : normalResidual A b x = 0
  · simp only [hz, if_true] at hp hq
    exact hp.2.trans hq.2.symm
  · simp only [hz, if_false] at hp hq
    obtain ⟨P, hP, rfl⟩ := hp.2
    obtain ⟨Q, hQ, rfl⟩ := hq.2
    rw [penrose_projection_unique hP hQ]

/-- The actual seven-by-three vertical stack, with a symbolic residual/iterate norm ratio. -/
def stackAt (η : ℝ) : Matrix (Fin 4 ⊕ Fin 3) (Fin 3) ℝ :=
  fun i j => match i with
  | Sum.inl i => witnessA i j
  | Sum.inr i => if i = j then η else 0

def gramDiagonal (η : ℝ) (j : Fin 3) : ℝ := ![(1 : ℝ), 36, 25] j + η ^ 2

def inverseGram (η : ℝ) : Mat 3 3 := Matrix.diagonal (fun j => (gramDiagonal η j)⁻¹)

def penroseAt (η : ℝ) : Matrix (Fin 3) (Fin 4 ⊕ Fin 3) ℝ :=
  inverseGram η * (stackAt η).transpose

lemma gramDiagonal_pos (η : ℝ) (j : Fin 3) : 0 < gramDiagonal η j := by
  fin_cases j <;> simp [gramDiagonal] <;> positivity

lemma stackAt_gram (η : ℝ) :
    (stackAt η).transpose * stackAt η = Matrix.diagonal (gramDiagonal η) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, stackAt, witnessA, gramDiagonal, Matrix.diagonal,
      Fintype.sum_sum_type, Fin.sum_univ_succ] <;> ring

lemma inverseGram_mul_gram (η : ℝ) :
    inverseGram η * Matrix.diagonal (gramDiagonal η) = 1 := by
  rw [inverseGram, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [Matrix.diagonal, (gramDiagonal_pos η i).ne']
  · simp [Matrix.diagonal, h]

lemma penroseAt_left_inverse (η : ℝ) : penroseAt η * stackAt η = 1 := by
  rw [penroseAt, Matrix.mul_assoc, stackAt_gram, inverseGram_mul_gram]

lemma stackAt_penrose_symmetric (η : ℝ) :
    (stackAt η * penroseAt η).transpose = stackAt η * penroseAt η := by
  simp [penroseAt, inverseGram, Matrix.transpose_mul, Matrix.mul_assoc]

lemma penroseAt_correct (η : ℝ) : IsMoorePenrose (stackAt η) (penroseAt η) := by
  refine ⟨?_, ?_, stackAt_penrose_symmetric η, ?_⟩
  · rw [Matrix.mul_assoc, penroseAt_left_inverse, Matrix.mul_one]
  · rw [penroseAt_left_inverse, Matrix.one_mul]
  · rw [penroseAt_left_inverse, Matrix.transpose_one]

lemma stacked_eq_stackAt (x : Vec 3) :
    stacked witnessA witnessB x = stackAt (‖residual witnessA witnessB x‖ / ‖x‖) := by
  ext i j
  cases i <;> simp [stacked, stackAt]

def padded (r : Vec 4) : EuclideanSpace ℝ (Fin 4 ⊕ Fin 3) :=
  WithLp.toLp 2 (Sum.elim (fun i => r i) (fun _ => 0))

set_option maxRecDepth 2048 in
lemma projection_norm_sq (η : ℝ) (r : Vec 4) :
    ‖(stackAt η * penroseAt η).toEuclideanLin (padded r)‖ ^ 2 =
      r 0 ^ 2 / (1 + η ^ 2) + 36 * r 1 ^ 2 / (36 + η ^ 2) +
        25 * r 2 ^ 2 / (25 + η ^ 2) := by
  have h₀ : (1 : ℝ) + η ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h₁ : (36 : ℝ) + η ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h₂ : (25 : ℝ) + η ^ 2 ≠ 0 := ne_of_gt (by positivity)
  simp only [Matrix.toEuclideanLin, penroseAt, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  simp only [Matrix.toLpLin_apply]
  simp [inverseGram, gramDiagonal, stackAt, padded, witnessA, Matrix.mul_apply,
    Matrix.mulVec, dotProduct,
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, Fin.sum_univ_succ]
  field_simp
  ring


lemma stackedResidual_eq_padded (x : Vec 3) :
    stackedResidual witnessA witnessB x = padded (residual witnessA witnessB x) := by
  ext i
  cases i <;> rfl

/-- The literal projected residual divided by the iterate norm. -/
def actualQ (x : Vec 3) : ℝ :=
  let η := ‖residual witnessA witnessB x‖ / ‖x‖
  ‖(stackAt η * penroseAt η).toEuclideanLin (padded (residual witnessA witnessB x))‖ / ‖x‖

lemma actualQ_nonneg (x : Vec 3) : 0 ≤ actualQ x := div_nonneg (norm_nonneg _) (norm_nonneg _)

lemma actualQ_approximation (x : Vec 3) (hx : x ≠ 0)
    (hr : normalResidual witnessA witnessB x ≠ 0) :
    IsApproximation witnessA witnessB x (actualQ x) := by
  refine ⟨hx, ?_⟩
  simp only [hr, if_false, stacked_eq_stackAt, stackedResidual_eq_padded]
  exact ⟨penroseAt _, penroseAt_correct _, rfl⟩

lemma actualQ_sq (x : Vec 3) :
    actualQ x ^ 2 =
      ((residual witnessA witnessB x) 0 ^ 2 /
          (1 + ‖residual witnessA witnessB x‖ ^ 2 / ‖x‖ ^ 2) +
        36 * (residual witnessA witnessB x) 1 ^ 2 /
          (36 + ‖residual witnessA witnessB x‖ ^ 2 / ‖x‖ ^ 2) +
        25 * (residual witnessA witnessB x) 2 ^ 2 /
          (25 + ‖residual witnessA witnessB x‖ ^ 2 / ‖x‖ ^ 2)) / ‖x‖ ^ 2 := by
  simp only [actualQ, div_pow, projection_norm_sq]

lemma actualQ_one_sq : actualQ witnessX₁ ^ 2 =
    (69694107852573439503892031925 : ℝ) / 69323394392991282508138323472 := by
  rw [actualQ_sq, witnessX₁_norm_sq, witness_residual_one_norm_sq, witness_residual_one]
  norm_num [Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three]

lemma actualQ_two_sq : actualQ witnessX₂ ^ 2 =
    (5430772101137459612205263871781350 : ℝ) / 5387955615790281743396033884265233 := by
  rw [actualQ_sq, witnessX₂_norm_sq, witness_residual_two_norm_sq, witness_residual_two]
  norm_num [Matrix.cons_val_succ', Matrix.cons_val_two, Matrix.cons_val_three]

/-- Unique values of the canonical Moore–Penrose approximation at both nonzero iterates. -/
theorem approximation_error_values :
    ∃ q₁ q₂ : ℝ,
      IsApproximation witnessA witnessB witnessX₁ q₁ ∧
      IsApproximation witnessA witnessB witnessX₂ q₂ ∧
      (∀ q, IsApproximation witnessA witnessB witnessX₁ q → q = q₁) ∧
      (∀ q, IsApproximation witnessA witnessB witnessX₂ q → q = q₂) ∧
      0 ≤ q₁ ∧ 0 ≤ q₂ ∧
      q₁ ^ 2 = (69694107852573439503892031925 : ℝ) / 69323394392991282508138323472 ∧
      q₂ ^ 2 = (5430772101137459612205263871781350 : ℝ) / 5387955615790281743396033884265233 := by
  have h₁ := actualQ_approximation witnessX₁ witnessX₁_ne_zero normalResidual_one_ne_zero
  have h₂ := actualQ_approximation witnessX₂ witnessX₂_ne_zero normalResidual_two_ne_zero
  exact ⟨actualQ witnessX₁, actualQ witnessX₂, h₁, h₂,
    fun _ h => approximation_unique h h₁, fun _ h => approximation_unique h h₂,
    actualQ_nonneg _, actualQ_nonneg _, actualQ_one_sq, actualQ_two_sq⟩

#assert_trust kernel penrose_projection_unique
#assert_trust kernel penroseAt_correct
#assert_trust kernel approximation_error_values
#print axioms penrose_projection_unique
#print axioms penroseAt_correct
#print axioms approximation_error_values

end NLA.IE17

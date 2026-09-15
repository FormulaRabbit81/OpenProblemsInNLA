/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Spectral

noncomputable section
open Matrix
open scoped BigOperators Matrix MatrixOrder
namespace NLA.SP05

lemma jordan_posDef {n : ℕ} {A B : Mat n} (hA : A.PosDef) (hB : B.PosDef) :
    (jordanMatrix A B).PosDef := (hA.kronecker hB).add (hB.kronecker hA)

lemma jordan_commutation {n : ℕ} (A B : Mat n) (v : Vec n) :
    commutationMatrix n *ᵥ (jordanMatrix A B *ᵥ v) =
      jordanMatrix A B *ᵥ (commutationMatrix n *ᵥ v) := by
  simp only [jordanMatrix, Matrix.add_mulVec, Matrix.mulVec_add,
    commutation_kronecker, add_comm]

lemma jordan_inverse_commutation {n : ℕ} {A B : Mat n}
    (hA : A.PosDef) (hB : B.PosDef) (v : Vec n) :
    commutationMatrix n *ᵥ ((jordanMatrix A B)⁻¹ *ᵥ v) =
      (jordanMatrix A B)⁻¹ *ᵥ (commutationMatrix n *ᵥ v) := by
  have hJ := jordan_posDef hA hB
  have hmul : jordanMatrix A B * (jordanMatrix A B)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hJ.isUnit)
  have hinv (z : Vec n) : jordanMatrix A B *ᵥ ((jordanMatrix A B)⁻¹ *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  apply Matrix.mulVec_injective_of_isUnit hJ.isUnit
  rw [← jordan_commutation, hinv, hinv]

lemma real_eigenmatrix_sign {n : ℕ} {P : Operator n} {r : ℝ} {v : Vec n}
    (hv : v ≠ 0) (he : P *ᵥ v = r • v)
    (hcomm : ∀ w : Vec n, commutationMatrix n *ᵥ (P *ᵥ w) =
      P *ᵥ (commutationMatrix n *ᵥ w)) :
    ∃ W : Mat n, W ≠ 0 ∧ (Wᵀ = W ∨ Wᵀ = -W) ∧
      P *ᵥ columnVec W = r • columnVec W := by
  obtain ⟨W, rfl⟩ := Matrix.vec_bijective.surjective v
  have hW : W ≠ 0 := by intro h; apply hv; simp [h]
  have he' : P *ᵥ columnVec W = r • columnVec W := he
  have het : P *ᵥ columnVec Wᵀ = r • columnVec Wᵀ := by
    rw [← commutation_columnVec, ← hcomm, he', Matrix.mulVec_smul, commutation_columnVec]
  by_cases hs : W + Wᵀ = 0
  · refine ⟨W, hW, Or.inr ?_, he'⟩
    exact eq_neg_of_add_eq_zero_right hs
  · refine ⟨W + Wᵀ, hs, Or.inl ?_, ?_⟩
    · simp [Matrix.transpose_add, add_comm]
    · simp only [columnVec, Matrix.vec_add, Matrix.mulVec_add, he', het, smul_add]

lemma jordan_inverse_top_sign (n : ℕ) (hn : 1 ≤ n) {A B : Mat n}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ r : ℝ, ∃ W : Mat n, 0 < r ∧ W ≠ 0 ∧ (Wᵀ = W ∨ Wᵀ = -W) ∧
      (jordanMatrix A B)⁻¹ *ᵥ columnVec W = r • columnVec W ∧
      (r • (1 : Operator n) - (jordanMatrix A B)⁻¹).PosSemidef := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨r, v, hr, hv, he, hS⟩ := real_spectral_max (jordan_posDef hA hB).inv
  obtain ⟨W, hW, hs, heW⟩ := real_eigenmatrix_sign hv he (jordan_inverse_commutation hA hB)
  exact ⟨r, W, hr, hW, hs, heW, hS⟩

lemma inverse_eigen_to_eigen {n : ℕ} {J : Operator n} (hJ : J.PosDef)
    {r : ℝ} (hr : 0 < r) {v : Vec n} (he : J⁻¹ *ᵥ v = r • v) :
    J *ᵥ v = r⁻¹ • v := by
  have hjp : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J ((Matrix.isUnit_iff_isUnit_det J).mp hJ.isUnit)
  have h := congrArg (fun w => J *ᵥ w) he
  rw [Matrix.mulVec_mulVec, hjp, Matrix.one_mulVec, Matrix.mulVec_smul] at h
  calc
    J *ᵥ v = r⁻¹ • (r • (J *ᵥ v)) := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    _ = r⁻¹ • v := by rw [← h]

lemma rayleigh_lower_of_slack {n : ℕ} {J : Operator n} {μ : ℝ}
    (hS : (J - μ • (1 : Operator n)).PosSemidef) {v : Vec n} (hv : v ≠ 0) :
    μ ≤ rayleigh J v := by
  have hs := hS.re_dotProduct_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, RCLike.re_to_real] at hs
  exact (le_div_iff₀ (dot_self_pos hv)).mpr (by linarith)

end NLA.SP05

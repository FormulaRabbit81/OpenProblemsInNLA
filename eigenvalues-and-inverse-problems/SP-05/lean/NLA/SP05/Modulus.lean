/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Sylvester

noncomputable section
open Matrix
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace NLA.SP05

/-- The real matrix action obtained by column unvectorization of the actual coefficient matrix. -/
def realMatrixAction {n : ℕ} (P : Operator n) (X : Mat n) : Mat n :=
  fun i j => (P *ᵥ columnVec X) (j,i)

/-- Its actual complex-linear extension, using entrywise complexification of the coefficients. -/
def complexMatrixAction {n : ℕ} (P : Operator n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (complexify P *ᵥ vec X) (j,i)

@[simp] theorem vec_realMatrixAction {n : ℕ} (P : Operator n) (X : Mat n) :
    columnVec (realMatrixAction P X) = P *ᵥ columnVec X := rfl

@[simp] theorem vec_complexMatrixAction {n : ℕ} (P : Operator n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    vec (complexMatrixAction P X) = complexify P *ᵥ vec X := rfl

@[simp] theorem complexMatrixAction_real {n : ℕ} (P : Operator n) (X : Mat n) :
    complexMatrixAction P (complexify X) = complexify (realMatrixAction P X) := by
  ext i j
  simp [complexMatrixAction, realMatrixAction, complexify, mulVec, dotProduct, vec]

/-- Real part of the genuine complex Frobenius pairing with the coefficient action. -/
def complexPairing {n : ℕ} (P : Operator n) (X Y : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (star (vec X) ⬝ᵥ (complexify P *ᵥ vec Y)).re

theorem complexPairing_trace {n : ℕ} (P : Operator n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    complexPairing P X Y = (Xᴴ * complexMatrixAction P Y).trace.re := by
  rw [complexPairing, ← vec_complexMatrixAction, star_vec_dotProduct_vec]

@[simp] theorem complexPairing_real {n : ℕ} (P : Operator n) (X Y : Mat n) :
    complexPairing P (complexify X) (complexify Y) =
      columnVec X ⬝ᵥ (P *ᵥ columnVec Y) := by
  simp [complexPairing, complexify, vec, mulVec, dotProduct, Complex.mul_re]

@[simp] theorem complexPairing_I {n : ℕ} (P : Operator n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    complexPairing P (Complex.I • X) (Complex.I • Y) = complexPairing P X Y := by
  simp [complexPairing, vec_smul, star_smul, mulVec_smul, dotProduct_smul,
    smul_dotProduct, Complex.conj_I]

/-- The trace of a product of two complex Hermitian PSD matrices is nonnegative. -/
theorem trace_product_posSemidef_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X*Y).trace.re := by
  let S := CFC.sqrt X
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)
  have hSS : S*S=X := CFC.sqrt_mul_sqrt_self X hX.nonneg
  have h := (hY.conjTranspose_mul_mul_same S).trace_nonneg
  rw [hS.isHermitian.eq, trace_mul_cycle, hSS] at h
  exact (Complex.nonneg_iff.mp h).1

/-- Both cross terms are nonnegative; self-adjointness of the coefficient action is unnecessary. -/
theorem complexPairing_posSemidef_nonneg {n : ℕ} (P : Operator n)
    (hcone : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
      (complexMatrixAction P X).PosSemidef)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ complexPairing P X Y := by
  rw [complexPairing_trace, hX.isHermitian.eq]
  exact trace_product_posSemidef_nonneg hX (hcone Y hY)

/-- The source modulus comparison on the full complex Hermitian cone. -/
theorem hermitian_modulus_pairing_le {n : ℕ} (P : Operator n)
    (hcone : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
      (complexMatrixAction P X).PosSemidef)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    complexPairing P H H ≤ complexPairing P (CFC.abs H) (CFC.abs H) := by
  have hp : H⁺.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)
  have hn : H⁻.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hpn := complexPairing_posSemidef_nonneg P hcone hp hn
  have hnp := complexPairing_posSemidef_nonneg P hcone hn hp
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have habs : H⁺ + H⁻ = CFC.abs H := CFC.posPart_add_negPart H hH.isSelfAdjoint
  have hexpand (U V : Matrix (Fin n) (Fin n) ℂ) :
      complexPairing P (U+V) (U+V) - complexPairing P (U-V) (U-V) =
      2 * complexPairing P U V + 2 * complexPairing P V U := by
    simp only [complexPairing, vec_add, vec_sub, star_add, star_sub, mulVec_add,
      mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct,
      Complex.add_re, Complex.sub_re]
    ring
  have hexpand' := hexpand H⁺ H⁻
  rw [habs, hdecomp] at hexpand'
  linarith

/-- Absolute value preserves the actual real Frobenius squared norm, including singular matrices. -/
theorem real_abs_vec_norm_sq {n : ℕ} (W : Mat n) :
    columnVec (CFC.abs W) ⬝ᵥ columnVec (CFC.abs W) = columnVec W ⬝ᵥ columnVec W := by
  have hAbs : (CFC.abs W).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg W)
  rw [vec_dotProduct_vec, vec_dotProduct_vec]
  congr 1
  rw [← conjTranspose_eq_transpose_of_trivial, hAbs.isHermitian.eq, ← pow_two, CFC.abs_sq]
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- Modulus replaces any symmetric or skew eigenmatrix by a real PSD matrix with no smaller quotient. -/
theorem modulus_quadratic_improves {n : ℕ} (P : Operator n)
    (hcone : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
      (complexMatrixAction P X).PosSemidef)
    (W : Mat n) (hW : W ≠ 0) (hsign : Wᵀ=W ∨ Wᵀ=-W) (r : ℝ)
    (heig : P *ᵥ columnVec W = r • columnVec W) :
    (CFC.abs W).PosSemidef ∧ CFC.abs W ≠ 0 ∧
    columnVec (CFC.abs W) ⬝ᵥ columnVec (CFC.abs W) = columnVec W ⬝ᵥ columnVec W ∧
    r * (columnVec (CFC.abs W) ⬝ᵥ columnVec (CFC.abs W)) ≤
      columnVec (CFC.abs W) ⬝ᵥ (P *ᵥ columnVec (CFC.abs W)) := by
  have hAbsne : CFC.abs W ≠ 0 := by
    intro hz
    have hzero : columnVec W ⬝ᵥ columnVec W = 0 := by
      rw [← real_abs_vec_norm_sq W, hz]
      simp
    exact hW (Matrix.vec_eq_zero_iff.mp (dotProduct_self_eq_zero.mp hzero))
  refine ⟨Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg W),
    hAbsne, real_abs_vec_norm_sq W, ?_⟩
  have hcompare : columnVec W ⬝ᵥ (P *ᵥ columnVec W) ≤
      columnVec (CFC.abs W) ⬝ᵥ (P *ᵥ columnVec (CFC.abs W)) := by
    rcases hsign with hs | hs
    · have hH : (complexify W).IsHermitian := by
        change (complexify W)ᴴ = complexify W
        rw [← complexify_conjTranspose, conjTranspose_eq_transpose_of_trivial, hs]
      have h := hermitian_modulus_pairing_le P hcone hH
      simpa only [← complexify_abs, complexPairing_real] using h
    · have hH : (Complex.I • complexify W).IsHermitian := by
        change (Complex.I • complexify W)ᴴ = Complex.I • complexify W
        rw [conjTranspose_smul, ← complexify_conjTranspose,
          conjTranspose_eq_transpose_of_trivial, hs]
        ext i j
        simp [complexify, Matrix.map_apply, Complex.conj_I]
      have h := hermitian_modulus_pairing_le P hcone hH
      simpa only [complexify_abs_I_smul, complexPairing_I, complexPairing_real] using h
  rw [real_abs_vec_norm_sq]
  simpa only [heig, dotProduct_smul, smul_eq_mul] using hcompare

#assert_trust kernel complexMatrixAction_real
#assert_trust kernel trace_product_posSemidef_nonneg
#assert_trust kernel hermitian_modulus_pairing_le
#assert_trust kernel modulus_quadratic_improves
#print axioms complexMatrixAction_real
#print axioms trace_product_posSemidef_nonneg
#print axioms hermitian_modulus_pairing_le
#print axioms modulus_quadratic_improves
end NLA.SP05

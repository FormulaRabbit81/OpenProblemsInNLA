/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Definitions
import LeanCert.Tactic

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLA.SP05

/-- Entrywise complexification, on any finite matrix index type. -/
def complexify {ι : Type*} (A : Matrix ι ι ℝ) : Matrix ι ι ℂ := A.map Complex.ofReal

@[simp] theorem complexify_apply {ι : Type*} (A : Matrix ι ι ℝ) (i j : ι) :
    complexify A i j = (A i j : ℂ) := rfl

/-- The actual entrywise map as a real star-algebra homomorphism. -/
def complexifyHom (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ where
  __ := (Algebra.ofId ℝ ℂ).mapMatrix
  map_star' A := by ext i j; simp [Matrix.star_apply]

@[simp] theorem complexifyHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : complexifyHom ι A = complexify A := rfl

theorem complexify_injective {ι : Type*} : Function.Injective (@complexify ι) :=
  Matrix.map_injective Complex.ofReal_injective

@[simp] theorem complexify_zero {ι : Type*} : complexify (0 : Matrix ι ι ℝ) = 0 := by
  ext i j; simp

@[simp] theorem complexify_eq_zero {ι : Type*} {A : Matrix ι ι ℝ} :
    complexify A = 0 ↔ A = 0 := by
  rw [← complexify_zero, complexify_injective.eq_iff]

@[simp] theorem complexify_add {ι : Type*} (A B : Matrix ι ι ℝ) :
    complexify (A+B) = complexify A + complexify B := by ext i j; simp

@[simp] theorem complexify_sub {ι : Type*} (A B : Matrix ι ι ℝ) :
    complexify (A-B) = complexify A - complexify B := by ext i j; simp

@[simp] theorem complexify_smul {ι : Type*} (r : ℝ) (A : Matrix ι ι ℝ) :
    complexify (r • A) = r • complexify A := by ext i j; simp

@[simp] theorem complexify_star {ι : Type*} (A : Matrix ι ι ℝ) :
    complexify (star A) = star (complexify A) := by ext i j; simp [Matrix.star_apply]

@[simp] theorem complexify_conjTranspose {ι : Type*} (A : Matrix ι ι ℝ) :
    complexify Aᴴ = (complexify A)ᴴ := complexify_star A

@[simp] theorem complexify_transpose {ι : Type*} (A : Matrix ι ι ℝ) :
    complexify Aᵀ = (complexify A)ᵀ := rfl

@[simp] theorem complexify_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    complexify (1 : Matrix ι ι ℝ) = 1 := (complexifyHom ι).map_one

@[simp] theorem complexify_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) : complexify (A*B) = complexify A * complexify B :=
  (complexifyHom ι).map_mul A B

theorem complexify_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : (complexify A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (map_nonneg (complexifyHom ι) hA.nonneg)

theorem complexify_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) : (complexify A).PosDef :=
  (complexify_posSemidef hA.posSemidef).posDef_iff_isUnit.mpr
    (hA.isUnit.map (complexifyHom ι))

@[simp] theorem complexify_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsUnit A) : complexify A⁻¹ = (complexify A)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← complexify_mul, Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA), complexify_one]

/-- Square-root naturality uses PSD preservation and uniqueness, including singular inputs. -/
theorem complexify_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    complexify (CFC.sqrt A) = CFC.sqrt (complexify A) := by
  symm
  apply CFC.sqrt_unique
  · rw [← complexify_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (complexify_posSemidef (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))).nonneg

/-- The complex modulus of a real matrix is the complexification of its real PSD modulus. -/
theorem complexify_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : complexify (CFC.abs A) = CFC.abs (complexify A) := by
  unfold CFC.abs
  have h := complexify_sqrt (Matrix.posSemidef_conjTranspose_mul_self A)
  change complexify (CFC.sqrt (star A * A)) = _ at h
  simpa only [complexify_mul, complexify_conjTranspose, Matrix.star_eq_conjTranspose] using h

/-- In particular the modulus of i times a real skew matrix is real; no nonsingularity is needed. -/
theorem complexify_abs_I_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : CFC.abs (Complex.I • complexify A) = complexify (CFC.abs A) := by
  rw [CFC.abs_smul, Complex.norm_I, one_smul, complexify_abs]

#assert_trust kernel complexify_posSemidef
#assert_trust kernel complexify_posDef
#assert_trust kernel complexify_inv
#assert_trust kernel complexify_sqrt
#assert_trust kernel complexify_abs_I_smul
#print axioms complexify_posSemidef
#print axioms complexify_posDef
#print axioms complexify_inv
#print axioms complexify_sqrt
#print axioms complexify_abs_I_smul
end NLA.SP05

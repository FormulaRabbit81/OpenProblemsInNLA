/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP05.Complexification
import Mathlib.Tactic.NoncommRing

noncomputable section
open Matrix
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace NLA.SP05

/-- Inverse positivity for a Hermitian Sylvester equation, by testing its eigenvectors. -/
theorem sylvester_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C X : Matrix ι ι ℂ} (hC : C.PosDef) (hX : X.IsHermitian)
    (hY : (C*X + X*C).PosSemidef) : X.PosSemidef := by
  rw [hX.posSemidef_iff_eigenvalues_nonneg]
  intro i
  let v : ι → ℂ := hX.eigenvectorBasis i
  let ev : ℝ := hX.eigenvalues i
  have hv : v ≠ 0 := by
    intro hz
    apply hX.eigenvectorBasis.orthonormal.ne_zero i
    ext j
    exact congrFun hz j
  have heig : X *ᵥ v = ev • v := hX.mulVec_eigenvectorBasis i
  have hleft : star v ᵥ* X = ev • star v := by
    calc
      star v ᵥ* X = star v ᵥ* Xᴴ := by rw [hX.eq]
      _ = star (X *ᵥ v) := by rw [vecMul_conjTranspose, star_star]
      _ = ev • star v := by rw [heig, star_smul, star_trivial]
  have hquad : star v ⬝ᵥ ((C*X+X*C) *ᵥ v) =
      (2*ev) • (star v ⬝ᵥ (C *ᵥ v)) := by
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, heig, mulVec_smul,
      dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec (star v) X (C *ᵥ v), hleft, smul_dotProduct]
    rw [← add_smul]
    congr 1
    ring
  have hnonneg := hY.re_dotProduct_nonneg v
  rw [hquad, RCLike.smul_re] at hnonneg
  have hpos := hC.re_dotProduct_pos hv
  change 0 ≤ ev
  nlinarith

/-- Positive definiteness makes the full complex Jordan equation injective. -/
theorem complex_jordan_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    Function.Injective (fun X : Matrix ι ι ℂ => A*X*B+B*X*A) := by
  let K := Matrix.kronecker Bᵀ A + Matrix.kronecker Aᵀ B
  have hK : K.PosDef := (hB.transpose.kronecker hA).add (hA.transpose.kronecker hB)
  intro X Y hXY
  apply Matrix.vec_inj.mp
  apply Matrix.mulVec_injective_of_isUnit hK.isUnit
  simpa only [K, Matrix.kronecker, add_mulVec, kronecker_mulVec_vec, transpose_transpose, ← vec_add] using
    congrArg Matrix.vec hXY

/-- Hermitian right-hand sides have Hermitian solutions, by uniqueness on the full matrix space. -/
theorem complex_jordan_preimage_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B X : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hY : (A*X*B+B*X*A).IsHermitian) : X.IsHermitian := by
  change Xᴴ = X
  apply complex_jordan_injective hA hB
  calc
    A*Xᴴ*B+B*Xᴴ*A = (A*X*B+B*X*A)ᴴ := by
      simp only [conjTranspose_add, conjTranspose_mul, hA.isHermitian.eq,
        hB.isHermitian.eq, mul_assoc, add_comm]
    _ = A*X*B+B*X*A := hY.eq

/-- The inverse of a positive-definite Jordan operator preserves the full complex Hermitian cone. -/
theorem complex_jordan_preimage_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B X : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hY : (A*X*B+B*X*A).PosSemidef) : X.PosSemidef := by
  have hX := complex_jordan_preimage_hermitian hA hB hY.isHermitian
  let U := CFC.sqrt B
  let V := U⁻¹
  have hUpsd : U.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hUunit : IsUnit U := (CFC.isUnit_sqrt_iff B hB.posSemidef.nonneg).mpr hB.isUnit
  have hU : U.PosDef := hUpsd.posDef_iff_isUnit.mpr hUunit
  have hV : V.PosDef := hU.inv
  have hUV : U*V=1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).mp hUunit)
  have hVU : V*U=1 := Matrix.nonsing_inv_mul U ((Matrix.isUnit_iff_isUnit_det U).mp hUunit)
  have hUU : U*U=B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hBV : B*V=U := by rw [← hUU, mul_assoc, hUV, mul_one]
  have hVB : V*B=U := by rw [← hUU, ← mul_assoc, hVU, one_mul]
  let C := V*A*V
  let S := U*X*U
  have hC : C.PosDef := by
    have h := hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hV.isUnit)
    simpa only [hV.isHermitian.eq] using h
  have hS : S.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul U hX
    simpa only [hU.isHermitian.eq] using h
  have hCS : C*S=V*A*X*U := by
    calc
      C*S = (V*A)*(V*U)*X*U := by dsimp [C,S]; noncomm_ring
      _ = V*A*X*U := by rw [hVU, mul_one]
  have hSC : S*C=U*X*A*V := by
    calc
      S*C = U*X*(U*V)*A*V := by dsimp [C,S]; noncomm_ring
      _ = U*X*A*V := by rw [hUV, mul_one]
  have hcong : V*(A*X*B+B*X*A)*V = C*S+S*C := by
    calc
      V*(A*X*B+B*X*A)*V = V*A*X*(B*V)+(V*B)*X*A*V := by noncomm_ring
      _ = C*S+S*C := by rw [hBV, hVB, hCS, hSC]
  have hSY : (C*S+S*C).PosSemidef := by
    have h := hY.conjTranspose_mul_mul_same V
    rw [hV.isHermitian.eq, hcong] at h
    exact h
  have hSpsd := sylvester_posSemidef hC hS hSY
  have h := hSpsd.conjTranspose_mul_mul_same V
  rw [hV.isHermitian.eq] at h
  have hback : V*S*V=X := by
    calc
      V*S*V = (V*U)*X*(U*V) := by dsimp [S]; noncomm_ring
      _ = X := by rw [hVU, hUV, one_mul, mul_one]
  rwa [hback] at h

/-- Equation form, with the actual right-hand side and no assumed Hermitian solution. -/
theorem complex_jordan_solution_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B X Y : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hY : Y.PosSemidef) (hEq : A*X*B+B*X*A=Y) : X.PosSemidef :=
  complex_jordan_preimage_posSemidef hA hB (hEq.symm ▸ hY)

#assert_trust kernel sylvester_posSemidef
#assert_trust kernel complex_jordan_injective
#assert_trust kernel complex_jordan_preimage_hermitian
#assert_trust kernel complex_jordan_solution_posSemidef
#print axioms sylvester_posSemidef
#print axioms complex_jordan_injective
#print axioms complex_jordan_preimage_hermitian
#print axioms complex_jordan_solution_posSemidef
end NLA.SP05

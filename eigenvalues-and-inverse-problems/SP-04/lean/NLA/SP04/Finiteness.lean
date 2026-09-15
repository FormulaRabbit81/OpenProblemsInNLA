/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Diagonal
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi

noncomputable section
open scoped BigOperators Matrix
open Polynomial
namespace NLA.SP04

set_option maxRecDepth 2048

abbrev TensorIndex := Fin 2 × Fin 2 × Fin 2

def scalarCompanion {R : Type*} [Ring R] (s c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![s, -c; 1, 0]

/-- The three companion matrices' tensor product, kept unexpanded. -/
def companionTensor (s : Fin 3 → ℝ) (c : ℝ) : Matrix TensorIndex TensorIndex ℝ :=
  fun i j => scalarCompanion (s 0) c i.1 j.1 *
    scalarCompanion (s 1) c i.2.1 j.2.1 * scalarCompanion (s 2) c i.2.2 j.2.2

def companionTensorPolynomial (s : Fin 3 → ℝ) : Matrix TensorIndex TensorIndex ℝ[X] :=
  fun i j => scalarCompanion (C (s 0)) X i.1 j.1 *
    scalarCompanion (C (s 1)) X i.2.1 j.2.1 * scalarCompanion (C (s 2)) X i.2.2 j.2.2

def stationaryEliminant (s : Fin 3 → ℝ) : ℝ[X] :=
  (1-companionTensorPolynomial s).det * (1+companionTensorPolynomial s).det

theorem companionTensorPolynomial_eval (s : Fin 3 → ℝ) (c : ℝ) :
    (evalRingHom c).mapMatrix (companionTensorPolynomial s) = companionTensor s c := by
  ext ⟨i0,i1,i2⟩ ⟨j0,j1,j2⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [companionTensorPolynomial, companionTensor, scalarCompanion]
  all_goals first | exact Or.inl (mul_comm _ _) | exact mul_comm _ _

theorem polynomial_eval_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ[X]) (c : ℝ) :
    A.det.eval c = ((evalRingHom c).mapMatrix A).det :=
  (evalRingHom c).map_det A

theorem polynomial_pair_det_eval {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ[X]) (c : ℝ) :
    ((1-A).det * (1+A).det).eval c =
      (1-(evalRingHom c).mapMatrix A).det * (1+(evalRingHom c).mapMatrix A).det := by
  simp only [Polynomial.eval_mul, polynomial_eval_det, map_sub, map_one, map_add]

set_option maxRecDepth 16384 in
theorem stationaryEliminant_eval (s : Fin 3 → ℝ) (c : ℝ) :
    (stationaryEliminant s).eval c =
      (1-companionTensor s c).det * (1+companionTensor s c).det := by
  have hmap := companionTensorPolynomial_eval s c
  unfold stationaryEliminant
  generalize companionTensorPolynomial s = A at hmap ⊢
  rw [polynomial_pair_det_eval, hmap]

def tensorColumn (s : Fin 3 → ℝ) (i : TensorIndex) : ℝ :=
  (if i.1=0 then s 0 else 1) * (if i.2.1=0 then s 1 else 1) * (if i.2.2=0 then s 2 else 1)

def tensorBasisRow (j : TensorIndex) : ℝ := if j=(0,0,0) then 1 else 0

theorem companionTensor_zero (s : Fin 3 → ℝ) :
    companionTensor s 0 = Matrix.replicateCol Unit (tensorColumn s) *
      Matrix.replicateRow Unit tensorBasisRow := by
  ext ⟨i0,i1,i2⟩ ⟨j0,j1,j2⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [companionTensor, scalarCompanion, Matrix.mul_apply, tensorColumn, tensorBasisRow,
      Matrix.replicateCol, Matrix.replicateRow]

theorem stationaryEliminant_at_zero (s : Fin 3 → ℝ) :
    (stationaryEliminant s).eval 0 = 1-(s 0*s 1*s 2)^2 := by
  rw [stationaryEliminant_eval, companionTensor_zero,
    Matrix.det_one_sub_mul_comm, Matrix.det_one_add_mul_comm]
  simp [Matrix.det_unique, Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow,
    tensorBasisRow, tensorColumn, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem stationaryEliminant_ne_zero (s : Fin 3 → ℝ) (hs : Admissible s) :
    stationaryEliminant s ≠ 0 := by
  intro hz
  have he := stationaryEliminant_at_zero s
  rw [hz, Polynomial.eval_zero] at he
  have hlarge : 1<s 0*s 1*s 2 := by
    have h0 := (scalar_admissible_bounds hs 0).1
    have h1 := (scalar_admissible_bounds hs 1).1
    have h2 := (scalar_admissible_bounds hs 2).1
    calc (1:ℝ)=1*1*1 := by ring
         _ < s 0*s 1*s 2 := by gcongr <;> linarith
  nlinarith only [he, hlarge]

def companionVector (x : ℝ) : Fin 2 → ℝ := ![x,1]

def companionTensorVector (x : Fin 3 → ℝ) : TensorIndex → ℝ :=
  fun i => companionVector (x 0) i.1 * companionVector (x 1) i.2.1 * companionVector (x 2) i.2.2

theorem scalarCompanion_eigenvector (s c x : ℝ) (hx : x^2-s*x+c=0) :
    scalarCompanion s c *ᵥ companionVector x = x • companionVector x := by
  ext i
  fin_cases i <;> simp [scalarCompanion, companionVector, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] <;> nlinarith

theorem companionTensor_eigenvector (s x : Fin 3 → ℝ) (c : ℝ)
    (hx : ∀ i, (x i)^2-s i*x i+c=0) :
    companionTensor s c *ᵥ companionTensorVector x = (x 0*x 1*x 2) • companionTensorVector x := by
  ext ⟨i0,i1,i2⟩
  have h0 := congrFun (scalarCompanion_eigenvector (s 0) c (x 0) (hx 0)) i0
  have h1 := congrFun (scalarCompanion_eigenvector (s 1) c (x 1) (hx 1)) i1
  have h2 := congrFun (scalarCompanion_eigenvector (s 2) c (x 2) (hx 2)) i2
  change (∑ j : TensorIndex, companionTensor s c (i0,i1,i2) j * companionTensorVector x j) =
    (x 0*x 1*x 2) * companionTensorVector x (i0,i1,i2)
  calc
    _ = ((scalarCompanion (s 0) c *ᵥ companionVector (x 0)) i0 *
         (scalarCompanion (s 1) c *ᵥ companionVector (x 1)) i1) *
         (scalarCompanion (s 2) c *ᵥ companionVector (x 2)) i2 := by
      simp only [companionTensor, companionTensorVector, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_two]
      ring
    _ = _ := by
      rw [h0,h1,h2]
      simp [companionTensorVector, Pi.smul_apply, smul_eq_mul]
      ring

theorem companionTensorVector_ne_zero (x : Fin 3 → ℝ) : companionTensorVector x ≠ 0 := by
  intro hz
  have h := congrFun hz (1,1,1)
  norm_num [companionTensorVector, companionVector] at h

theorem scalar_stationary_eliminant (s x : Fin 3 → ℝ) (c : ℝ)
    (hq : ∀ i, (x i)^2-s i*x i+c=0) (hp : |∏ i, x i|=1) :
    (stationaryEliminant s).eval c=0 := by
  have he := companionTensor_eigenvector s x c hq
  have hv := companionTensorVector_ne_zero x
  have hprod : x 0*x 1*x 2=1 ∨ x 0*x 1*x 2= -1 := by
    simpa [Fin.prod_univ_three] using (abs_eq (by norm_num : (0:ℝ)≤1)).mp hp
  rw [stationaryEliminant_eval]
  rcases hprod with hprod|hprod
  · have hz : (1-companionTensor s c).det=0 :=
      (Matrix.exists_mulVec_eq_zero_iff).mp ⟨companionTensorVector x, hv, by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, he, hprod, one_smul, sub_self]⟩
    simp [hz]
  · have hz : (1+companionTensor s c).det=0 :=
      (Matrix.exists_mulVec_eq_zero_iff).mp ⟨companionTensorVector x, hv, by
        rw [Matrix.add_mulVec, Matrix.one_mulVec, he, hprod, neg_one_smul, add_neg_cancel]⟩
    simp [hz]

theorem scalar_quadratic_finite (s c : ℝ) : {x : ℝ | x^2-s*x+c=0}.Finite := by
  let p : ℝ[X] := X^2-C s*X+C c
  have hp : p≠0 := by
    intro hz
    have h := congrArg (fun q : ℝ[X] => q.coeff 2) hz
    norm_num [p, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul] at h
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  simpa [p, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow] using hfin

/-- Finiteness of the entire stationary pair set, with no assumed finite search list. -/
theorem diagonal_stationary_finite (s : Fin 3 → ℝ) (hs : Admissible s) :
    (stationaryPairs (Matrix.diagonal s)).Finite := by
  apply Set.Finite.of_finite_fibers Prod.snd
  · have hf := Polynomial.finite_setOfPred_isRoot (stationaryEliminant_ne_zero s hs)
    apply hf.subset
    rintro c ⟨⟨Y,d⟩, hY, rfl⟩
    obtain ⟨x, hYx, hq, hp⟩ := (all_diagonal_stationary_iff s hs Y d).mp hY
    exact scalar_stationary_eliminant s x d hq hp
  · intro c _
    have htuples : {x : Fin 3 → ℝ | ∀ i, (x i)^2-s i*x i+c=0}.Finite :=
      Set.Finite.pi' (fun i => scalar_quadratic_finite (s i) c)
    have himage := htuples.image (fun x => (Matrix.diagonal x,c))
    apply himage.subset
    rintro ⟨Y,d⟩ ⟨hY,hd⟩
    have hdc : d=c := hd
    subst d
    obtain ⟨x, hYx, hq, hp⟩ := (all_diagonal_stationary_iff s hs Y c).mp hY
    exact ⟨x,hq,by simp [hYx]⟩

#assert_trust kernel stationaryEliminant_at_zero
#assert_trust kernel scalar_stationary_eliminant
#assert_trust kernel diagonal_stationary_finite
#print axioms stationaryEliminant_at_zero
#print axioms scalar_stationary_eliminant
#print axioms diagonal_stationary_finite

end NLA.SP04

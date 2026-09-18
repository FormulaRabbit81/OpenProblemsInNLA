/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.SolutionPolynomial
import NLA.MF18.PairingVectors
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem unregularized_factorization {n : ℕ} (C R X : Mat n)
    (hX : X.det ≠ 0) (heq : X + C.conjTranspose * X⁻¹ * C = R) (z : ℂ) :
    pencilValue C C.conjTranspose R z =
      (z • (C.conjTranspose * X⁻¹) - 1) * X *
        (z • (1 : Mat n) - X⁻¹ * C) := by
  exact pencil_factorization C C.conjTranspose R X hX heq z

theorem unregularized_polynomial_factorization {n : ℕ} (C R X : Mat n)
    (hX : X.det ≠ 0) (heq : X + C.conjTranspose * X⁻¹ * C = R) :
    unregularizedPolynomial C R = Polynomial.C X.det *
      (complementaryPolynomial C.conjTranspose X * (X⁻¹ * C).charpoly) := by
  exact pencil_polynomial_factorization C C.conjTranspose R X hX heq

theorem unregularized_left_factor {n : ℕ} (C X : Mat n) (hX : X.det ≠ 0) (z : ℂ) :
    (z • (C.conjTranspose * X⁻¹) - 1) * X = z • C.conjTranspose - X := by
  rw [sub_mul, smul_mul_assoc, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hX), Matrix.mul_one]

theorem isRoot_charpoly_of_mulVec {n : ℕ} (S : Mat n) (lam : ℂ) (v : Vec n)
    (hv : v ≠ 0) (heig : S.mulVec v = lam • v) : S.charpoly.IsRoot lam := by
  have hev : Module.End.HasEigenvector S.toLin' lam v :=
    ⟨Module.End.mem_eigenspace_iff.mpr heig, hv⟩
  have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly S.toLin' lam).mp
    (Module.End.hasEigenvalue_of_hasEigenvector hev)
  simpa only [Matrix.charpoly_toLin'] using he

theorem simple_root_factor_separation {n : ℕ} (C R X : Mat n)
    (hX : X.det ≠ 0) (heq : X + C.conjTranspose * X⁻¹ * C = R)
    (lam : ℂ) (hsimple : (unregularizedPolynomial C R).rootMultiplicity lam = 1)
    (v : Vec n) (hv : v ≠ 0) (heig : (X⁻¹ * C).mulVec v = lam • v) :
    (X⁻¹ * C).charpoly.rootMultiplicity lam = 1 ∧
    (lam • C.conjTranspose - X).det ≠ 0 := by
  have hq := complementary_ne_zero C.conjTranspose X
  have hS := (Matrix.charpoly_monic (X⁻¹ * C)).ne_zero
  have hprod := mul_ne_zero hq hS
  have hC : Polynomial.C X.det ≠ 0 := Polynomial.C_ne_zero.mpr hX
  have hm := hsimple
  rw [unregularized_polynomial_factorization C R X hX heq,
    Polynomial.rootMultiplicity_mul (mul_ne_zero hC hprod), Polynomial.rootMultiplicity_C,
    Polynomial.rootMultiplicity_mul hprod, zero_add] at hm
  have hpos : 0 < (X⁻¹ * C).charpoly.rootMultiplicity lam :=
    (Polynomial.rootMultiplicity_pos hS).mpr (isRoot_charpoly_of_mulVec _ lam v hv heig)
  have hsone : (X⁻¹ * C).charpoly.rootMultiplicity lam = 1 := by omega
  have hqzero : (complementaryPolynomial C.conjTranspose X).rootMultiplicity lam = 0 := by omega
  have hqeval : (complementaryPolynomial C.conjTranspose X).eval lam ≠ 0 := by
    intro hz
    have hp := (Polynomial.rootMultiplicity_pos hq).mpr hz
    omega
  refine ⟨hsone, ?_⟩
  rw [← unregularized_left_factor C X hX lam, Matrix.det_mul,
    ← complementary_evaluation]
  exact mul_ne_zero hqeval hX

theorem pairing_sub_matrix {n : ℕ} (A B : Mat n) (v w : Vec n) :
    pairing (A - B) v w = pairing A v w - pairing B v w := by
  simp only [pairing_eq_dotProduct, Matrix.sub_mulVec, dotProduct_sub]

theorem pairing_mul_matrix {n : ℕ} (A B : Mat n) (v w : Vec n) :
    pairing (A * B) v w = pairing A v (B.mulVec w) := by
  simp only [pairing_eq_dotProduct, Matrix.mulVec_mulVec]

#print axioms simple_root_factor_separation

end NLA.MF18

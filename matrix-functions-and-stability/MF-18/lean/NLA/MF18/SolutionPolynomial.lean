/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
-/
import NLA.MF18.PencilAlgebra
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem eval_charpoly_smul {n : ℕ} (M : Mat n) (z : ℂ) :
    M.charpoly.eval z = (z • (1 : Mat n) - M).det := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem complementary_evaluation {n : ℕ} (B X : Mat n) (z : ℂ) :
    (complementaryPolynomial B X).eval z = (z • (B * X⁻¹) - 1).det := by
  let M : Matrix (Fin n) (Fin n) CPoly := fun i j =>
    Polynomial.C ((B * X⁻¹) i j) * Polynomial.X - Polynomial.C ((1 : Mat n) i j)
  -- Expose complementaryPolynomial as det M and polynomial evaluation as its ring homomorphism.
  change (Polynomial.evalRingHom z) M.det = _
  calc
    _ = (M.map (Polynomial.evalRingHom z)).det := (Polynomial.evalRingHom z).map_det M
    _ = _ := by
      congr 1
      ext i j
      -- At (i,j), unfold M and matrix mapping into evaluation of the displayed linear polynomial.
      change (Polynomial.C ((B * X⁻¹) i j) * Polynomial.X -
        Polynomial.C ((1 : Mat n) i j)).eval z = (z • (B * X⁻¹) - 1) i j
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring

theorem complementary_ne_zero {n : ℕ} (B X : Mat n) :
    complementaryPolynomial B X ≠ 0 := by
  have he : (complementaryPolynomial B X).eval 0 ≠ 0 := by
    rw [complementary_evaluation]
    simp only [zero_smul, zero_sub, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro hz
  exact he (by rw [hz, Polynomial.eval_zero])

/-- Taking determinants in the common pencil factorization preserves the full polynomial. -/
theorem pencil_polynomial_factorization {n : ℕ} (A B Q X : Mat n)
    (hX : X.det ≠ 0) (heq : X + B * X⁻¹ * A = Q) :
    scalarPencil A B Q =
      Polynomial.C X.det * (complementaryPolynomial B X * (X⁻¹ * A).charpoly) := by
  apply Polynomial.funext
  intro z
  rw [pencil_evaluation, pencil_factorization A B Q X hX heq z]
  simp only [Matrix.det_mul, Polynomial.eval_mul, Polynomial.eval_C,
    complementary_evaluation, eval_charpoly_smul]
  ring

theorem solution_polynomial_factorization {n : ℕ} (C D R P : Mat n) (η : ℝ) (X : Mat n)
    (h : IsStabilizingSolution C D R P η X) :
    regularizedPolynomial C D R P η =
      Polynomial.C X.det * (complementaryPolynomial (regularizedB C D η) X *
        (X⁻¹ * regularizedA C D η).charpoly) := by
  exact pencil_polynomial_factorization (regularizedA C D η) (regularizedB C D η)
    (regularizedQ R P η) X h.1 h.2.1

theorem diskRootCount_mul (p q : CPoly) (hpq : p * q ≠ 0) :
    diskRootCount (p * q) = diskRootCount p + diskRootCount q := by
  classical
  unfold diskRootCount
  rw [Polynomial.roots_mul hpq, Multiset.filter_add, Multiset.card_add]

theorem diskRootCount_C_mul (a : ℂ) (ha : a ≠ 0) (p : CPoly) :
    diskRootCount (Polynomial.C a * p) = diskRootCount p := by
  classical
  unfold diskRootCount
  rw [Polynomial.roots_C_mul p ha]

theorem strictStable_disk_count {n : ℕ} (S : Mat n) (hS : StrictStable S) :
    diskRootCount S.charpoly = n := by
  classical
  unfold diskRootCount
  rw [Multiset.filter_eq_self.mpr (fun z hz => hS z (Polynomial.isRoot_of_mem_roots hz)),
    IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem diskRootCount_zero_no_root (p : CPoly) (hp : p ≠ 0)
    (hcount : diskRootCount p = 0) (z : ℂ) (hz : ‖z‖ < 1) : p.eval z ≠ 0 := by
  classical
  intro heval
  have hmem : z ∈ p.roots.filter (fun w => ‖w‖ < 1) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hp).mpr heval, hz⟩
  have hempty : p.roots.filter (fun w => ‖w‖ < 1) = 0 :=
    Multiset.card_eq_zero.mp hcount
  simpa only [hempty, Multiset.notMem_zero] using hmem

#print axioms pencil_polynomial_factorization
#print axioms solution_polynomial_factorization
#print axioms strictStable_disk_count

end NLA.MF18

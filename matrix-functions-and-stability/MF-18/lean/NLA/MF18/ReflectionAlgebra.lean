/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

Fixed-grade reflection preserves the reciprocal symmetry even when the
leading coefficient matrix is singular. All operations are finite algebra.
-/
import NLA.MF18.PencilAlgebra
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem reflect_finset_sum {ι : Type*} (s : Finset ι) (p : ι → CPoly) (N : ℕ) :
    (∑ i ∈ s, p i).reflect N = ∑ i ∈ s, (p i).reflect N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Polynomial.reflect_add, ih]

theorem natDegree_prod_bound {ι : Type*} (s : Finset ι) (p : ι → CPoly) (d : ℕ)
    (hd : ∀ i ∈ s, (p i).natDegree ≤ d) : (∏ i ∈ s, p i).natDegree ≤ d * s.card := by
  calc
    _ ≤ ∑ i ∈ s, (p i).natDegree := Polynomial.natDegree_prod_le s p
    _ ≤ ∑ _i ∈ s, d := Finset.sum_le_sum hd
    _ = _ := by simp [Nat.mul_comm]

theorem reflect_finset_prod {ι : Type*} (s : Finset ι) (p : ι → CPoly) (d : ℕ)
    (hd : ∀ i ∈ s, (p i).natDegree ≤ d) :
    (∏ i ∈ s, p i).reflect (d * s.card) = ∏ i ∈ s, (p i).reflect d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, (p j).natDegree ≤ d := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hi' := hd i (Finset.mem_insert_self i s)
    simp only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    -- Split the inserted product grade into d and d * s.card, the grades required by reflect_mul.
    rw [show d * (s.card + 1) = d + d * s.card by ring,
      Polynomial.reflect_mul (p i) (∏ j ∈ s, p j) hi' (natDegree_prod_bound s p d hs), ih hs]

theorem reflect_det {n : ℕ} (M : Matrix (Fin n) (Fin n) CPoly) (d : ℕ)
    (hd : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.reflect (d * n) = Matrix.det (fun i j => (M i j).reflect d) := by
  classical
  let N : Matrix (Fin n) (Fin n) CPoly := fun i j => (M i j).reflect d
  -- Name the entrywise-reflected matrix by N so det_apply receives an explicitly typed matrix.
  change M.det.reflect (d * n) = N.det
  rw [Matrix.det_apply M, Matrix.det_apply N, reflect_finset_sum]
  apply Finset.sum_congr rfl
  intro σ _
  dsimp only [N]
  have hp := reflect_finset_prod (Finset.univ : Finset (Fin n)) (fun i => M (σ i) i) d
    (fun i _ => hd (σ i) i)
  simp only [Finset.card_univ, Fintype.card_fin] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [hs, one_smul] using hp
  · simpa only [hs, Units.neg_smul, one_smul, Polynomial.reflect_neg] using congrArg Neg.neg hp

theorem unregularized_reflection {n : ℕ} (C R : Mat n) (hR : R.IsHermitian) :
    (unregularizedPolynomial C R).reflect (2 * n) =
      (unregularizedPolynomial C R).map (starRingEnd ℂ) := by
  let M := matrixPolynomial C C.conjTranspose R
  have hd : ∀ i j, (M i j).natDegree ≤ 2 := by
    intro i j
    dsimp only [M, matrixPolynomial]
    compute_degree
  have hx : (Polynomial.X : CPoly).reflect 2 = Polynomial.X := by
    -- Reversing the degree-one monomial at fixed grade two leaves its exponent equal to one.
    simpa only [pow_one, show Polynomial.revAt 2 1 = 1 by decide] using
      (Polynomial.reflect_monomial 2 1 (R := ℂ))
  have hentry : (fun i j => (M i j).reflect 2) =
      M.transpose.map (Polynomial.mapRingHom (starRingEnd ℂ)) := by
    apply Matrix.ext
    intro i j
    -- Expose the (i,j) entry of the reflected matrix and the (j,i) entry of its coefficient conjugate.
    change (matrixPolynomial C C.conjTranspose R i j).reflect 2 =
      (matrixPolynomial C C.conjTranspose R j i).map (starRingEnd ℂ)
    simp only [matrixPolynomial, Polynomial.reflect_add, Polynomial.reflect_sub,
      Polynomial.reflect_C_mul, Polynomial.reflect_C, hx,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, starRingEnd_apply, Matrix.conjTranspose_apply,
      star_star, hR.apply i j]
    norm_num [Polynomial.reflect_monomial, Polynomial.revAt_le]
    ring
  -- UnregularizedPolynomial is the determinant of the local polynomial matrix M on both sides.
  change M.det.reflect (2 * n) = M.det.map (starRingEnd ℂ)
  rw [reflect_det M 2 hd, hentry]
  have he := (Polynomial.mapRingHom (starRingEnd ℂ)).map_det M.transpose
  rw [Matrix.det_transpose] at he
  exact he.symm

#print axioms unregularized_reflection

end NLA.MF18

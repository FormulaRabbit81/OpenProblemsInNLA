/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The literal sorted-minor definitions and exterior-basis multiplication proof are
adapted from George Stepaniants's accepted MF06 CompoundAlgebra.lean. Mathlib's
exterior basis and dual-coordinate construction retain their original authorship.
The new adjoint, unitary and diagonal bridges use the actual complex matrix
operations. No row-sum norm estimate is imported as a spectral norm theorem.
-/
import NLA.MI24.Definitions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

abbrev ExteriorIndex (n k : ℕ) := Set.powersetCard (Fin n) k

def compoundDim (n k : ℕ) : ℕ := Fintype.card (ExteriorIndex n k)

def compoundIndex (n k : ℕ) (i : Fin (compoundDim n k)) : ExteriorIndex n k :=
  (Fintype.equivFin (ExteriorIndex n k)).symm i

def minorCoordinate (n k : ℕ) (i : Fin (compoundDim n k)) : Fin k ↪o Fin n :=
  Set.powersetCard.ofFinEmbEquiv.symm (compoundIndex n k i)

def compoundMatrix {n : ℕ} (k : ℕ) (A : Mat n) : Mat (compoundDim n k) :=
  fun i j => Matrix.det (A.submatrix (minorCoordinate n k i) (minorCoordinate n k j))

lemma compound_dimensions (n k : ℕ) :
    compoundDim n k = Nat.choose n k ∧ (k ≤ n → 1 ≤ compoundDim n k) := by
  have hcard : compoundDim n k = Nat.choose n k := by
    unfold compoundDim ExteriorIndex
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card]
    simp
  refine ⟨hcard, ?_⟩
  intro hk
  rw [hcard]
  exact Nat.choose_pos hk

lemma compound_coordinate_semantics {n : ℕ} (k : ℕ) (A : Mat n)
    (i j : Fin (compoundDim n k)) :
    compoundMatrix k A i j =
      ((Pi.basisFun ℂ (Fin n)).exteriorPower k).repr
        (exteriorPower.map k (Matrix.toLin' A)
          (((Pi.basisFun ℂ (Fin n)).exteriorPower k) (compoundIndex n k j)))
        (compoundIndex n k i) := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  unfold exteriorPower.ιMulti_family
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  have hmatrix :
      (Matrix.of fun a b : Fin k =>
        (Pi.basisFun ℂ (Fin n)).coord (minorCoordinate n k i b)
          ((Matrix.toLin' A) ((Pi.basisFun ℂ (Fin n)) (minorCoordinate n k j a)))) =
      (A.submatrix (minorCoordinate n k i) (minorCoordinate n k j))ᵀ := by
    ext a b
    simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
      Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
  -- The exterior dual determinant has transposed row/column coordinates.
  change Matrix.det (A.submatrix (minorCoordinate n k i) (minorCoordinate n k j)) = _
  change _ = Matrix.det (Matrix.of fun a b : Fin k =>
    (Pi.basisFun ℂ (Fin n)).coord (minorCoordinate n k i b)
      ((Matrix.toLin' A) ((Pi.basisFun ℂ (Fin n)) (minorCoordinate n k j a))))
  rw [hmatrix, Matrix.det_transpose]

def compoundBasis (n k : ℕ) :
    Module.Basis (Fin (compoundDim n k)) ℂ (⋀[ℂ]^k (Fin n → ℂ)) :=
  ((Pi.basisFun ℂ (Fin n)).exteriorPower k).reindex
    (Fintype.equivFin (ExteriorIndex n k))

lemma compoundMatrix_eq_toMatrix {n : ℕ} (k : ℕ) (A : Mat n) :
    compoundMatrix k A = LinearMap.toMatrix (compoundBasis n k) (compoundBasis n k)
      (exteriorPower.map k (Matrix.toLin' A)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  dsimp only [compoundBasis]
  erw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  exact compound_coordinate_semantics k A i j

lemma compoundMatrix_one (n k : ℕ) : compoundMatrix k (1 : Mat n) = 1 := by
  rw [compoundMatrix_eq_toMatrix, Matrix.toLin'_one, exteriorPower.map_id,
    LinearMap.toMatrix_id]

lemma compoundMatrix_mul {n : ℕ} (k : ℕ) (A B : Mat n) :
    compoundMatrix k (A * B) = compoundMatrix k A * compoundMatrix k B := by
  rw [compoundMatrix_eq_toMatrix, Matrix.toLin'_mul, exteriorPower.map_comp,
    LinearMap.toMatrix_comp (compoundBasis n k) (compoundBasis n k) (compoundBasis n k),
    ← compoundMatrix_eq_toMatrix, ← compoundMatrix_eq_toMatrix]

lemma compoundMatrix_star {n : ℕ} (k : ℕ) (A : Mat n) :
    compoundMatrix k (star A) = star (compoundMatrix k A) := by
  ext i j
  -- At a compound entry, expose the determinant of the indexed minor;
  -- matrix star also swaps the row/column indices, matching det_conjTranspose.
  change Matrix.det ((star A).submatrix (minorCoordinate n k i) (minorCoordinate n k j)) =
    star (Matrix.det (A.submatrix (minorCoordinate n k j) (minorCoordinate n k i)))
  rw [← Matrix.det_conjTranspose]
  congr 1

lemma compoundMatrix_mem_unitary {n : ℕ} (k : ℕ) (U : unitary (Mat n)) :
    compoundMatrix k (U : Mat n) ∈ unitary (Mat (compoundDim n k)) := by
  constructor
  · rw [← compoundMatrix_star, ← compoundMatrix_mul,
      Unitary.coe_star_mul_self, compoundMatrix_one]
  · rw [← compoundMatrix_star, ← compoundMatrix_mul,
      -- Specialize the second unitary subtype identity to its underlying
      -- matrix, so the preceding compoundMatrix_mul rewrite can consume it.
      show (U : Mat n) * star (U : Mat n) = 1 from U.property.2,
      compoundMatrix_one]

def compoundUnitary {n : ℕ} (k : ℕ) (U : unitary (Mat n)) :
    unitary (Mat (compoundDim n k)) :=
  ⟨compoundMatrix k (U : Mat n), compoundMatrix_mem_unitary k U⟩

lemma compoundMatrix_diagonal {n : ℕ} (k : ℕ) (x : Fin n → ℂ) :
    compoundMatrix k (Matrix.diagonal x) =
      Matrix.diagonal (fun i : Fin (compoundDim n k) =>
        ∏ a : Fin k, x (minorCoordinate n k i a)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    -- Expose the same-index compound entry as its principal minor;
    -- submatrix_diagonal then uses injectivity of the chosen minor coordinates.
    change Matrix.det ((Matrix.diagonal x).submatrix
      (minorCoordinate n k i) (minorCoordinate n k i)) = _
    rw [Matrix.submatrix_diagonal x _ (minorCoordinate n k i).injective,
      Matrix.det_diagonal, Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hindex : compoundIndex n k i ≠ compoundIndex n k j := by
      intro h
      exact hij ((Fintype.equivFin (ExteriorIndex n k)).symm.injective h)
    obtain ⟨z, hzi, hzj⟩ :=
      (Set.powersetCard.exists_mem_notMem_iff_ne _ _).mp hindex
    obtain ⟨a, ha⟩ :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (compoundIndex n k i) z).mpr hzi
    -- Expose the distinct-index compound entry as a determinant, with
    -- the right diagonal-matrix entry already reduced to zero.
    change Matrix.det ((Matrix.diagonal x).submatrix
      (minorCoordinate n k i) (minorCoordinate n k j)) = 0
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    -- Expose one entry of the selected minor row in the original diagonal
    -- matrix, where unequal original indices force that entry to vanish.
    change Matrix.diagonal x (minorCoordinate n k i a) (minorCoordinate n k j b) = 0
    apply Matrix.diagonal_apply_ne
    intro heq
    apply hzj
    apply (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (compoundIndex n k j) z).mp
    exact ⟨b, heq.symm.trans ha⟩

end NLA.MI24

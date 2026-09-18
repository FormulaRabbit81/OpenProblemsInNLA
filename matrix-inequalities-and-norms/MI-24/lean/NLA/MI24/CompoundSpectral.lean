/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The compound of a positive matrix has an explicit unitary diagonalization with
all k-fold eigenvalue products. Positive definiteness and real spectral powers
follow from this actual decomposition, including negative powers. Multiplication
then transports the two literal Heron comparison matrices to every compound degree.
-/
import NLA.MI24.CompoundAlgebra
import NLA.MI24.DiagonalPowers
import NLA.MI24.TraceSpectral
import NLA.MI24.HeronNorm

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

def compoundDiagonal {n : ℕ} (k : ℕ) (x : Fin n → ℝ)
    (i : Fin (compoundDim n k)) : ℝ :=
  ∏ a : Fin k, x (minorCoordinate n k i a)

lemma compoundDiagonal_pos {n : ℕ} (k : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (i : Fin (compoundDim n k)) :
    0 < compoundDiagonal k x i := Finset.prod_pos fun _ _ => hx _

lemma compoundMatrix_diagonal_real {n : ℕ} (k : ℕ) (x : Fin n → ℝ) :
    compoundMatrix k (Matrix.diagonal (fun i => (x i : ℂ))) =
      Matrix.diagonal (fun i => (compoundDiagonal k x i : ℂ)) := by
  rw [compoundMatrix_diagonal]
  congr 1
  funext i
  exact (Complex.ofReal_prod _ _).symm

lemma compound_spectral_decomposition {n : ℕ} (k : ℕ) (A : Mat n)
    (hA : A.PosDef) :
    compoundMatrix k A =
      (compoundUnitary k hA.isHermitian.eigenvectorUnitary : Mat (compoundDim n k)) *
        Matrix.diagonal (fun i => (compoundDiagonal k hA.isHermitian.eigenvalues i : ℂ)) *
          star (compoundUnitary k hA.isHermitian.eigenvectorUnitary : Mat (compoundDim n k)) := by
  have hdecomp := spectralPower_spectral_decomposition A hA.posSemidef 1
  rw [spectralPower_one A hA] at hdecomp
  simp only [Real.rpow_one] at hdecomp
  calc
    compoundMatrix k A = compoundMatrix k
        ((hA.isHermitian.eigenvectorUnitary : Mat n) *
          Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) *
            star (hA.isHermitian.eigenvectorUnitary : Mat n)) := congrArg _ hdecomp
    _ = _ := by
      rw [compoundMatrix_mul, compoundMatrix_mul, compoundMatrix_star,
        compoundMatrix_diagonal_real]
      rfl

lemma compoundMatrix_posDef {n : ℕ} (k : ℕ) (A : Mat n) (hA : A.PosDef) :
    (compoundMatrix k A).PosDef := by
  rw [compound_spectral_decomposition k A hA]
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (Unitary.isUnit_coe (U := compoundUnitary k hA.isHermitian.eigenvectorUnitary))).mpr
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast compoundDiagonal_pos k hA.isHermitian.eigenvalues hA.eigenvalues_pos i

lemma compoundMatrix_spectralPower {n : ℕ} (k : ℕ) (A : Mat n)
    (hA : A.PosDef) (r : ℝ) :
    compoundMatrix k (spectralPower A r) = spectralPower (compoundMatrix k A) r := by
  let U := compoundUnitary k hA.isHermitian.eigenvectorUnitary
  let x := compoundDiagonal k hA.isHermitian.eigenvalues
  have hx (i : Fin (compoundDim n k)) : 0 < x i :=
    compoundDiagonal_pos k _ hA.eigenvalues_pos i
  have hd : (Matrix.diagonal (fun i => (x i : ℂ))).PosDef :=
    Matrix.PosDef.diagonal fun i => by exact_mod_cast hx i
  have hrprod (i : Fin (compoundDim n k)) :
      compoundDiagonal k (fun j => hA.isHermitian.eigenvalues j ^ r) i = x i ^ r := by
    exact Real.finsetProd_rpow Finset.univ
      (fun a : Fin k => hA.isHermitian.eigenvalues (minorCoordinate n k i a))
      (fun a _ => (hA.eigenvalues_pos _).le) r
  calc
    compoundMatrix k (spectralPower A r) =
        (U : Mat (compoundDim n k)) * Matrix.diagonal (fun i => ((x i ^ r : ℝ) : ℂ)) *
          star (U : Mat (compoundDim n k)) := by
      -- The spectral decomposition writes the adjoint as conjugate transpose.
      -- Use Mathlib's matrix-star bridge before the existing compoundMatrix_star.
      rw [spectralPower_spectral_decomposition A hA.posSemidef r,
        compoundMatrix_mul, compoundMatrix_mul, ← Matrix.star_eq_conjTranspose,
        compoundMatrix_star, compoundMatrix_diagonal_real]
      simp only [hrprod]
      rfl
    _ = spectralPower ((U : Mat (compoundDim n k)) *
        Matrix.diagonal (fun i => (x i : ℂ)) * star (U : Mat (compoundDim n k))) r := by
      rw [spectralPower_unitary_conjugate U _ hd r,
        spectralPower_diagonal x (fun i => (hx i).le) r]
    _ = spectralPower (compoundMatrix k A) r := by
      rw [compound_spectral_decomposition k A hA]

lemma compoundMatrix_weightedHeronSource {n : ℕ} (k : ℕ) (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) :
    compoundMatrix k (weightedHeronSource P D p) =
      weightedHeronSource (compoundMatrix k P) (compoundMatrix k D) p := by
  unfold weightedHeronSource
  rw [compoundMatrix_mul, compoundMatrix_mul,
    compoundMatrix_spectralPower k P hP,
    compoundMatrix_spectralPower k _ (geometric_inner_posDef P D hP hD),
    compoundMatrix_mul, compoundMatrix_mul,
    compoundMatrix_spectralPower k P hP]

lemma compoundMatrix_weightedHeronTarget {n : ℕ} (k : ℕ) (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) :
    compoundMatrix k (weightedHeronTarget P D p) =
      weightedHeronTarget (compoundMatrix k P) (compoundMatrix k D) p := by
  unfold weightedHeronTarget
  rw [compoundMatrix_mul, compoundMatrix_mul,
    compoundMatrix_spectralPower k P hP, compoundMatrix_spectralPower k D hD]

lemma weightedHeron_compound_norm_le {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (P D : Mat n) (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    infinitySchattenNorm (compoundMatrix k (weightedHeronSource P D p)) ≤
      infinitySchattenNorm (compoundMatrix k (weightedHeronTarget P D p)) := by
  rw [compoundMatrix_weightedHeronSource k P D hP hD,
    compoundMatrix_weightedHeronTarget k P D hP hD]
  exact weightedHeronSource_norm_le ((compound_dimensions n k).2 hk)
    _ _ (compoundMatrix_posDef k P hP) (compoundMatrix_posDef k D hD) p hp

end NLA.MI24

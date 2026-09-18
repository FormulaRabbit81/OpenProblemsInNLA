/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The Gram matrix may be singular. Only nonnegative exponents are composed, and
Real.rpow_div_two_eq_sqrt includes zero eigenvalues. The sorted Gram spectrum
is identified with Mathlib's actual singular values, preserving multiplicities.
-/
import NLA.MI24.TraceSpectral
import NLA.MI24.PolarModulus
import NLA.MI24.OperatorNorm

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

lemma singularValue_eq_sqrt_gram {n : ℕ} (X : Mat n)
    (i : Fin (Fintype.card (Fin n))) :
    singularValue X i.val =
      Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self X).isHermitian.eigenvalues₀ i) := by
  unfold singularValue
  rw [Matrix.IsHermitian.eigenvalues₀]
  simp only [toEuclideanLin_gram]
  exact (Matrix.toEuclideanLin X).singularValues_fin finrank_euclideanSpace i

lemma spectralPower_modulus {n : ℕ} (X : Mat n) (p : ℝ) (hp : 0 ≤ p) :
    spectralPower (matrixModulus X) p = spectralPower (Xᴴ * X) (p / 2) := by
  rw [matrixModulus_eq_spectralPower]
  -- Expose the spectralPower wrapper as nested CFC.rpow applications;
  -- this is the exact API of the nonnegative-exponent composition theorem.
  change CFC.rpow (CFC.rpow (Xᴴ * X) (1 / 2)) p = CFC.rpow (Xᴴ * X) (p / 2)
  -- Normalize the real product (1/2)*p to p/2 to align that CFC theorem
  -- with the frozen modulus-power exponent.
  simpa only [CFC.rpow_eq_pow, show ((1 / 2 : ℝ) * p) = p / 2 by ring] using
    CFC.rpow_rpow_of_exponent_nonneg (Xᴴ * X) (1 / 2 : ℝ) p (by norm_num) hp
      (Matrix.posSemidef_conjTranspose_mul_self X).nonneg

lemma traceReal_modulus_power {n : ℕ} (X : Mat n) (p : ℝ) (hp : 0 ≤ p) :
    traceReal (spectralPower (matrixModulus X) p) =
      ∑ i : Fin n, Real.rpow (singularValue X i.val) p := by
  let hG := Matrix.posSemidef_conjTranspose_mul_self X
  rw [spectralPower_modulus X p hp, traceReal_spectralPower_sorted _ hG]
  have hsum :
      (∑ i : Fin (Fintype.card (Fin n)), hG.isHermitian.eigenvalues₀ i ^ (p / 2)) =
        ∑ i : Fin (Fintype.card (Fin n)), Real.rpow (singularValue X i.val) p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.rpow_div_two_eq_sqrt p (posSemidef_eigenvalues₀_nonneg _ hG i),
      singularValue_eq_sqrt_gram]
    simp only [Real.rpow_eq_pow]
  calc
    _ = ∑ i : Fin (Fintype.card (Fin n)), Real.rpow (singularValue X i.val) p := hsum
    _ = ∑ i : Fin n, Real.rpow (singularValue X i.val) p := by
      apply Fintype.sum_equiv (Fin.castOrderIso (Fintype.card_fin n)).toEquiv
      intro i
      rfl

theorem finite_schatten_semantics {n : ℕ} (hn : 1 ≤ n) (X : Mat n)
    (p : ℝ) (hp : 1 ≤ p) :
    finiteSchattenNorm p X =
      Real.rpow (∑ i : Fin n, Real.rpow (singularValue X i.val) p) (1 / p) := by
  -- The spectral identity also holds in dimension zero; retain the frozen boundary.
  clear hn
  -- Unfold only finiteSchattenNorm to its trace/modulus definition;
  -- traceReal_modulus_power then rewrites the actual inner trace.
  change Real.rpow (traceReal (spectralPower (matrixModulus X) p)) (1 / p) = _
  rw [traceReal_modulus_power X p (by linarith)]

end NLA.MI24

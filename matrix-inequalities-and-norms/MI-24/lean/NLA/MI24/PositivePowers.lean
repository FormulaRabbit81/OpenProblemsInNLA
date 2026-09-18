/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Power identities used in the Schatten duality argument stay on nonnegative
exponents and hence allow singular positive semidefinite matrices. Every scalar
power with fractional exponent is explicitly real or contains a real variable.
-/
import NLA.MI24.PowerScaling
import Mathlib.Data.Real.ConjExponents

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

lemma spectralPower_posSemidef {n : ℕ} (A : Mat n) (r : ℝ) :
    (spectralPower A r).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (spectralPower_nonneg A r)

lemma spectralPower_mul_nonneg {n : ℕ} (A : Mat n) (hA : A.PosSemidef)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    spectralPower A r * spectralPower A s = spectralPower A (r + s) := by
  have hpow (t : ℝ) : spectralPower A t = cfc (fun x : ℝ => x ^ t) A :=
    CFC.rpow_eq_cfc_real hA.nonneg
  rw [hpow r, hpow s, hpow (r + s), ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  exact (Real.rpow_add_of_nonneg (spectrum_nonneg_of_nonneg hA.nonneg hx) hr hs).symm

lemma spectralPower_comp_nonneg {n : ℕ} (A : Mat n) (hA : A.PosSemidef)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    spectralPower (spectralPower A r) s = spectralPower A (r * s) := by
  simpa only [spectralPower, CFC.rpow_eq_pow] using
    CFC.rpow_rpow_of_exponent_nonneg A r s hr hs hA.nonneg

lemma mul_spectralPower_predecessor {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) (p : ℝ) (hp : 1 ≤ p) :
    A * spectralPower A (p - 1) = spectralPower A p := by
  have h := spectralPower_mul_nonneg A hA 1 (p - 1) (by norm_num) (by linarith)
  have hone : spectralPower A 1 = A := CFC.rpow_one A hA.nonneg
  -- Normalize the real exponent 1 + (p - 1) to p after combining powers;
  -- this lets the first-power identity replace only the factor A^1.
  rwa [hone, show (1 + (p - 1) : ℝ) = p by ring] at h

lemma finiteSchattenNorm_one_of_posSemidef {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) : finiteSchattenNorm 1 A = traceReal A := by
  rw [finiteSchattenNorm_of_posSemidef A hA]
  have hone : spectralPower A 1 = A := CFC.rpow_one A hA.nonneg
  rw [hone]
  norm_num

lemma finiteSchattenNorm_power_conjugate {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) (p q : ℝ) (hpq : p.HolderConjugate q) :
    finiteSchattenNorm q (spectralPower A (p - 1)) =
      (traceReal (spectralPower A p)) ^ (1 / q) := by
  rw [finiteSchattenNorm_of_posSemidef _ (spectralPower_posSemidef A _),
    spectralPower_comp_nonneg A hA (p - 1) q hpq.sub_one_pos.le hpq.symm.nonneg,
    hpq.sub_one_mul_conj]

/-- This scalar cancellation handles a zero trace separately; in the positive
case its cancelled factor is proved strictly positive. -/
lemma holder_trace_cancel (a b p q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) (h : a ≤ b * a ^ (1 / q)) :
    a ^ (1 / p) ≤ b := by
  by_cases ha0 : a = 0
  · simpa only [ha0, Real.zero_rpow (ne_of_gt hpq.one_div_pos)] using hb
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have heq : a ^ (1 / p) * a ^ (1 / q) = a := by
      rw [← Real.rpow_add hapos, one_div, one_div, hpq.inv_add_inv_eq_one, Real.rpow_one]
    apply le_of_mul_le_mul_right (a := a ^ (1 / q))
      (by rwa [heq]) (Real.rpow_pos_of_pos hapos _)

end NLA.MI24

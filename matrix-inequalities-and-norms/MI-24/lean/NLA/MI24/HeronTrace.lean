/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The explicit half-power fixed point and two weighted trace comparisons reduce
the normalized Heron theorem to trace Young. Its strictly positive weight is
proved for every real p >= 1; cancellation therefore includes p = 1.
-/
import NLA.MI24.WeightedTrace
import NLA.MI24.TraceYoung
import NLA.MI24.HalfFixedPoint

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma traceReal_smul_ofReal {n : ℕ} (Z : Mat n) (c : ℝ) :
    traceReal ((c : ℂ) • Z) = c * traceReal Z := by
  simp only [traceReal, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma traceReal_half {n : ℕ} (Z : Mat n) :
    traceReal ((1 / 2 : ℂ) • Z) = (1 / 2 : ℝ) * traceReal Z := by
  simpa using traceReal_smul_ofReal Z (1 / 2)

lemma traceReal_mul_half_add {n : ℕ} (Z U V : Mat n) :
    traceReal (Z * ((1 / 2 : ℂ) • (U + V))) =
      (1 / 2 : ℝ) * (traceReal (Z * U) + traceReal (Z * V)) := by
  rw [mul_smul_comm, traceReal_half]
  simp only [mul_add, traceReal, Matrix.trace_add, Complex.add_re]

theorem heron_trace_comparison {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    traceReal (spectralPower (powerHalfP A B) p) ≤
      traceReal (spectralPower (powerHalfQ A B) p) := by
  let P := powerHalfP A B
  let Q := powerHalfQ A B
  have hP : P.PosDef := (matrix_means_posdef hn A B hA hB).2.2.1
  have hQ : Q.PosDef := (matrix_means_posdef hn A B hA hB).2.2.2.1
  have hfixed : P = (1 / 2 : ℂ) • (geometricMean P A + geometricMean P B) :=
    power_half_fixed_point hn A B hA hB
  have hQsqrt : spectralPower Q (1 / 2) =
      (1 / 2 : ℂ) • (spectralPower A (1 / 2) + spectralPower B (1 / 2)) :=
    power_half_sqrt_q hn A B hA hB
  have hPP : spectralPower P (p - 1) * P = spectralPower P p := by
    simpa only [spectralPower_one P hP, sub_add_cancel] using
      spectralPower_mul P hP (p - 1) 1
  have hleft : traceReal (spectralPower P p) = (1 / 2 : ℝ) *
      (traceReal (spectralPower P (p - 1) * geometricMean P A) +
        traceReal (spectralPower P (p - 1) * geometricMean P B)) := by
    calc
      _ = traceReal (spectralPower P (p - 1) * P) := congrArg traceReal hPP.symm
      _ = traceReal (spectralPower P (p - 1) *
          ((1 / 2 : ℂ) • (geometricMean P A + geometricMean P B))) :=
        congrArg (fun Z => traceReal (spectralPower P (p - 1) * Z)) hfixed
      _ = _ := traceReal_mul_half_add _ _ _
  have hright : traceReal (spectralPower P (p - 1 / 2) * spectralPower Q (1 / 2)) =
      (1 / 2 : ℝ) *
        (traceReal (spectralPower P (p - 1 / 2) * spectralPower A (1 / 2)) +
          traceReal (spectralPower P (p - 1 / 2) * spectralPower B (1 / 2))) := by
    rw [hQsqrt, traceReal_mul_half_add]
  have hsum := add_le_add
    (weighted_geometric_trace hn P A hP hA p hp)
    (weighted_geometric_trace hn P B hP hB p hp)
  have hfirst : traceReal (spectralPower P p) ≤
      traceReal (spectralPower P (p - 1 / 2) * spectralPower Q (1 / 2)) := by
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hfinal := hfirst.trans (trace_young_half hn P Q hP hQ p hp)
  have hweight := youngWeight_pos p hp
  -- Use the local P/Q names for the two original half-power means;
  -- the goal then has exactly the trace terms in hfinal and its Young bound.
  change traceReal (spectralPower P p) ≤ traceReal (spectralPower Q p)
  nlinarith

end NLA.MI24

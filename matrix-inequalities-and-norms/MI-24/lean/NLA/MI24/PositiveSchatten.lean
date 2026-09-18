/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Order monotonicity and the triangle inequality are proved on the actual PSD
Schatten formula. The p=1 endpoint uses trace linearity. For p>1, trace Holder
and the explicit positive power (p-1) give the dual comparison, with the zero
trace handled by holder_trace_cancel. No abstract norm axioms are premises.
-/
import NLA.MI24.TraceHolder
import NLA.MI24.PositivePowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

theorem positive_schatten_monotone {n : ℕ} (hn : 1 ≤ n) (U V : Mat n)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (hUV : U ≤ V)
    (p : ℝ) (hp : 1 ≤ p) : finiteSchattenNorm p U ≤ finiteSchattenNorm p V := by
  clear hn
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst p
    rw [finiteSchattenNorm_one_of_posSemidef U hU,
      finiteSchattenNorm_one_of_posSemidef V hV]
    simpa only [mul_one] using traceReal_mul_order U V 1 hUV Matrix.PosSemidef.one
  · let q := Real.conjExponent p
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
    have hD := spectralPower_posSemidef U (p - 1)
    have horder := traceReal_mul_order U V (spectralPower U (p - 1)) hUV hD
    rw [mul_spectralPower_predecessor U hU p hp] at horder
    have hholder := positive_trace_holder V (spectralPower U (p - 1)) hV hD p q hpq
    rw [finiteSchattenNorm_power_conjugate U hU p q hpq] at hholder
    rw [finiteSchattenNorm_of_posSemidef U hU]
    exact holder_trace_cancel _ _ p q (traceReal_spectralPower_nonneg U hU p)
      (finiteSchattenNorm_nonneg V p) hpq (horder.trans hholder)

theorem positive_schatten_triangle {n : ℕ} (hn : 1 ≤ n) (U V : Mat n)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (p : ℝ) (hp : 1 ≤ p) :
    finiteSchattenNorm p (U + V) ≤ finiteSchattenNorm p U + finiteSchattenNorm p V := by
  clear hn
  have hS : (U + V).PosSemidef := hU.add hV
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst p
    rw [finiteSchattenNorm_one_of_posSemidef (U + V) hS,
      finiteSchattenNorm_one_of_posSemidef U hU,
      finiteSchattenNorm_one_of_posSemidef V hV]
    simp only [traceReal, Matrix.trace_add, Complex.add_re, le_refl]
  · let q := Real.conjExponent p
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
    have hD := spectralPower_posSemidef (U + V) (p - 1)
    have hu := positive_trace_holder U (spectralPower (U + V) (p - 1)) hU hD p q hpq
    have hv := positive_trace_holder V (spectralPower (U + V) (p - 1)) hV hD p q hpq
    rw [finiteSchattenNorm_power_conjugate (U + V) hS p q hpq] at hu hv
    have hsum := add_le_add hu hv
    have hleft : traceReal (U * spectralPower (U + V) (p - 1)) +
        traceReal (V * spectralPower (U + V) (p - 1)) =
          traceReal (spectralPower (U + V) p) := by
      rw [← mul_spectralPower_predecessor (U + V) hS p hp]
      simp only [add_mul, traceReal, Matrix.trace_add, Complex.add_re]
    rw [hleft, ← add_mul] at hsum
    rw [finiteSchattenNorm_of_posSemidef (U + V) hS]
    exact holder_trace_cancel _ _ p q (traceReal_spectralPower_nonneg (U + V) hS p)
      (add_nonneg (finiteSchattenNorm_nonneg U p) (finiteSchattenNorm_nonneg V p)) hpq hsum

end NLA.MI24

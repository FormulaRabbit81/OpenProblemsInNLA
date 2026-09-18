/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The full weighted geometric trace comparison is obtained from the proved Furuta
order implication at every compound degree, the actual compound norm formula,
and the scalar prefix-product-to-sum theorem. Both trace identifications are
explicit cyclic trace calculations on the original CFC matrix expressions.
-/
import NLA.MI24.CompoundNorm
import NLA.MI24.ScalarLogMajorization

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma traceReal_spectral_sandwich {n : ℕ} (P Z : Mat n) (hP : P.PosDef) (a : ℝ) :
    traceReal (spectralPower P a * Z * spectralPower P a) =
      traceReal (spectralPower P (a + a) * Z) := by
  unfold traceReal
  rw [Matrix.trace_mul_cycle, spectralPower_mul P hP]

lemma weightedHeronSource_trace {n : ℕ} (P D : Mat n) (hP : P.PosDef) (p : ℝ) :
    traceReal (weightedHeronSource P D p) =
      traceReal (spectralPower P (p - 1) * geometricMean P D) := by
  let C := spectralPower (spectralPower P (-1 / 2) * D *
    spectralPower P (-1 / 2)) (1 / 2)
  have hpower : spectralPower P (1 / 2) *
      (spectralPower P (p - 1) * spectralPower P (1 / 2)) = spectralPower P p := by
    rw [← mul_assoc, spectralPower_mul P hP, spectralPower_mul P hP]
    congr 1
    ring
  have htrace : traceReal (spectralPower P (p - 1) * geometricMean P D) =
      traceReal (spectralPower P p * C) := by
    calc
      _ = traceReal ((spectralPower P (p - 1) * spectralPower P (1 / 2)) * C *
          spectralPower P (1 / 2)) := by simp only [geometricMean, C, mul_assoc]
      _ = traceReal ((spectralPower P (1 / 2) *
          (spectralPower P (p - 1) * spectralPower P (1 / 2))) * C) :=
        congrArg Complex.re (Matrix.trace_mul_cycle _ _ _)
      _ = _ := by rw [hpower]
  rw [htrace]
  -- Expose weightedHeronSource as the P^(p/2) sandwich in the local C;
  -- the cyclic trace lemma then applies directly to these named factors.
  change traceReal (spectralPower P (p / 2) * C * spectralPower P (p / 2)) = _
  rw [traceReal_spectral_sandwich P C hP,
    -- Combine the two real half-exponents to p after cycling the trace.
    show (p / 2 + p / 2 : ℝ) = p by ring]

lemma weightedHeronTarget_trace {n : ℕ} (P D : Mat n) (hP : P.PosDef) (p : ℝ) :
    traceReal (weightedHeronTarget P D p) =
      traceReal (spectralPower P (p - 1 / 2) * spectralPower D (1 / 2)) := by
  unfold weightedHeronTarget
  rw [traceReal_spectral_sandwich P _ hP,
    -- Combine the two real half-exponents to p - 1/2 after cycling the
    -- weighted target; this is an explicit ring-normalization equality.
    show ((p - 1 / 2) / 2 + (p - 1 / 2) / 2 : ℝ) = p - 1 / 2 by ring]

lemma weightedHeronSource_trace_le {n : ℕ} (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    traceReal (weightedHeronSource P D p) ≤ traceReal (weightedHeronTarget P D p) := by
  let hS := weightedHeronSource_posDef P D hP hD p
  let hT := weightedHeronTarget_posDef P D hP hD p
  rw [traceReal_eq_sum_sortedSpectrum _ hS, traceReal_eq_sum_sortedSpectrum _ hT]
  apply sum_le_sum_of_prefix_prod_le
    (sortedSpectrum (weightedHeronSource P D p) hS)
    (sortedSpectrum (weightedHeronTarget P D p) hT)
    (sortedSpectrum_pos _ hS) (sortedSpectrum_pos _ hT) (sortedSpectrum_antitone _ hS)
  intro k hk
  have h := weightedHeron_compound_norm_le k hk P D hP hD p hp
  rw [infinitySchattenNorm_compound_eq_prefix k hk _ hS,
    infinitySchattenNorm_compound_eq_prefix k hk _ hT] at h
  exact h

theorem weighted_geometric_trace {n : ℕ} (hn : 1 ≤ n) (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    traceReal (spectralPower P (p - 1) * geometricMean P D) ≤
      traceReal (spectralPower P (p - 1 / 2) * spectralPower D (1 / 2)) := by
  clear hn
  rw [← weightedHeronSource_trace P D hP p, ← weightedHeronTarget_trace P D hP p]
  exact weightedHeronSource_trace_le P D hP hD p hp

end NLA.MI24

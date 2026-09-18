/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Scalar weighted AM--GM is applied to each pair of eigenvalues. The concrete
unitary overlap weights are then summed using both proved marginals. The actual
complement weight premise consumes the kernel-checked LeanCert interval theorem.
-/
import NLA.MI24.TraceOverlap
import NLA.MI24.Numerical
import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma scalar_young_half (x y p : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 1 ≤ p) :
    x ^ (p - 1 / 2) * y ^ (1 / 2 : ℝ) ≤
      (1 - youngWeight p) * x ^ p + youngWeight p * y ^ p := by
  have hp0 : p ≠ 0 := by linarith
  have htheta : p * youngWeight p = 1 / 2 := by
    unfold youngWeight
    field_simp [hp0]
  have hcomplement : p * (1 - youngWeight p) = p - 1 / 2 := by
    rw [mul_sub, mul_one, htheta]
  have hc : 0 ≤ 1 - youngWeight p :=
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (youngWeight_complement_bounds p hp).1
  have h := Real.geom_mean_le_arith_mean2_weighted hc (youngWeight_pos p hp).le
    (Real.rpow_nonneg hx p) (Real.rpow_nonneg hy p)
    -- Supply the exact real sum of the two complementary Young weights;
    -- the weighted arithmetic-geometric mean theorem requires this equality.
    (show (1 - youngWeight p) + youngWeight p = 1 by ring)
  rwa [← Real.rpow_mul hx, ← Real.rpow_mul hy, hcomplement, htheta] at h

theorem trace_young_half {n : ℕ} (hn : 1 ≤ n) (P Q : Mat n)
    (hP : P.PosDef) (hQ : Q.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    traceReal (spectralPower P (p - 1 / 2) * spectralPower Q (1 / 2)) ≤
      (1 - youngWeight p) * traceReal (spectralPower P p) +
        youngWeight p * traceReal (spectralPower Q p) := by
  clear hn
  rw [traceReal_spectralPower_product P Q hP.posSemidef hQ.posSemidef,
    traceReal_spectralPower P hP.posSemidef, traceReal_spectralPower Q hQ.posSemidef]
  let U := star hP.isHermitian.eigenvectorUnitary * hQ.isHermitian.eigenvectorUnitary
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        ((1 - youngWeight p) * hP.isHermitian.eigenvalues i ^ p +
          youngWeight p * hQ.isHermitian.eigenvalues j ^ p) *
            unitaryOverlapWeight U i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (scalar_young_half _ _ p (hP.posSemidef.eigenvalues_nonneg i)
          (hQ.posSemidef.eigenvalues_nonneg j) hp) (unitaryOverlapWeight_nonneg U i j)
    _ = _ := unitaryOverlapWeight_marginals U
      (fun i => hP.isHermitian.eigenvalues i ^ p)
      (fun j => hQ.isHermitian.eigenvalues j ^ p) (1 - youngWeight p) (youngWeight p)

end NLA.MI24

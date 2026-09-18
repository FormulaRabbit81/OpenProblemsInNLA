/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Passage from the proved normalized trace inequality to every finite real
Schatten p >= 1 uses only the positive trace formula and positive homogeneity.
-/
import NLA.MI24.HeronTrace
import NLA.MI24.PowerScaling

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

theorem heron_comparison_finite {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) (hp : 1 ≤ p) :
    finiteSchattenNorm p (heronEndpoint A B) ≤
      finiteSchattenNorm p (A + B + heronCross A B) := by
  have hmeans := matrix_means_posdef hn A B hA hB
  have hP := hmeans.2.2.1
  have hQ := hmeans.2.2.2.1
  have hE := hmeans.2.2.2.2.1
  have hC := hmeans.2.2.2.2.2.1
  have hnorm : finiteSchattenNorm p (powerHalfP A B) ≤
      finiteSchattenNorm p (powerHalfQ A B) := by
    rw [finiteSchattenNorm_of_posSemidef _ hP.posSemidef,
      finiteSchattenNorm_of_posSemidef _ hQ.posSemidef]
    exact Real.rpow_le_rpow (traceReal_spectralPower_nonneg _ hP.posSemidef p)
      (heron_trace_comparison hn A B hA hB p hp) (by positivity)
  unfold powerHalfP powerHalfQ at hnorm
  -- Expose the complex quarter as a real cast so positive_schatten_smul
  -- applies to both positive endpoint matrices with the same real scale.
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num,
    positive_schatten_smul hn _ hE.posSemidef p hp (1 / 4) (by norm_num),
    positive_schatten_smul hn _ hC.posSemidef p hp (1 / 4) (by norm_num)] at hnorm
  linarith

end NLA.MI24

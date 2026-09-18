/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The infinity endpoint is proved by a finite-power contradiction. For PSD matrices,
the largest eigenvalue to the m-th power lies below the trace, and the trace lies
below n times that largest power. If two operator norms were in the wrong order,
an explicitly existing natural power of their ratio would exceed n. Thus no
unproved Schatten-to-operator-norm limit is assumed.
-/
import NLA.MI24.HeronTrace
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma eigenvalue_le_infinitySchattenNorm {n : ℕ} (A : Mat n) (hA : A.PosSemidef)
    (i : Fin n) : hA.isHermitian.eigenvalues i ≤ infinitySchattenNorm A := by
  rw [infinitySchattenNorm_eq_eigenvalueNorm A hA.isHermitian]
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
    using norm_le_pi_norm (fun j => (hA.isHermitian.eigenvalues j : ℂ)) i

lemma infinitySchattenNorm_natPower_le_trace {n : ℕ} (hn : 1 ≤ n)
    (A : Mat n) (hA : A.PosSemidef) (m : ℕ) :
    infinitySchattenNorm A ^ m ≤ traceReal (spectralPower A (m : ℝ)) := by
  let i0 : Fin (Fintype.card (Fin n)) := ⟨0, by simpa using Nat.succ_le_iff.mp hn⟩
  have hnorm : infinitySchattenNorm A = hA.isHermitian.eigenvalues₀ i0 :=
    infinitySchattenNorm_posSemidef_eq_first hn A hA
  rw [hnorm, traceReal_spectralPower_sorted A hA]
  simp only [Real.rpow_natCast]
  exact Finset.single_le_sum
    (fun j _ => pow_nonneg (posSemidef_eigenvalues₀_nonneg A hA j) m)
    (Finset.mem_univ i0)

lemma trace_natPower_le_dimension_mul_norm {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) (m : ℕ) :
    traceReal (spectralPower A (m : ℝ)) ≤ (n : ℝ) * infinitySchattenNorm A ^ m := by
  rw [traceReal_spectralPower A hA]
  simp only [Real.rpow_natCast]
  calc
    _ ≤ ∑ _i : Fin n, infinitySchattenNorm A ^ m := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (hA.eigenvalues_nonneg i) (eigenvalue_le_infinitySchattenNorm A hA i) m
    _ = _ := by simp

lemma positive_infinity_le_of_trace_powers {n : ℕ} (hn : 1 ≤ n) (U V : Mat n)
    (hU : U.PosDef) (hV : V.PosDef)
    (htrace : ∀ p : ℝ, 1 ≤ p →
      traceReal (spectralPower U p) ≤ traceReal (spectralPower V p)) :
    infinitySchattenNorm U ≤ infinitySchattenNorm V := by
  by_contra hwrong
  have hv := infinitySchattenNorm_pos hn V hV
  have hratio : 1 < infinitySchattenNorm U / infinitySchattenNorm V :=
    (one_lt_div hv).mpr (lt_of_not_ge hwrong)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (n : ℝ) hratio
  have hm1 : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hm
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbound : infinitySchattenNorm U ^ m ≤
      (n : ℝ) * infinitySchattenNorm V ^ m :=
    (infinitySchattenNorm_natPower_le_trace hn U hU.posSemidef m).trans
      ((htrace (m : ℝ) (by exact_mod_cast hm1)).trans
        (trace_natPower_le_dimension_mul_norm V hV.posSemidef m))
  rw [div_pow] at hm
  exact (not_lt_of_ge hbound) ((lt_div_iff₀ (pow_pos hv m)).mp hm)

theorem heron_comparison_infinity {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) :
    infinitySchattenNorm (heronEndpoint A B) ≤
      infinitySchattenNorm (A + B + heronCross A B) := by
  have hmeans := matrix_means_posdef hn A B hA hB
  have hnorm := positive_infinity_le_of_trace_powers hn (powerHalfP A B) (powerHalfQ A B)
    hmeans.2.2.1 hmeans.2.2.2.1 (heron_trace_comparison hn A B hA hB)
  unfold powerHalfP powerHalfQ at hnorm
  -- Expose the complex quarter as a real cast, aligning both mean
  -- scalings with infinitySchattenNorm_smul_pos before cancellation.
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num,
    infinitySchattenNorm_smul_pos _ (1 / 4) (by norm_num),
    infinitySchattenNorm_smul_pos _ (1 / 4) (by norm_num)] at hnorm
  linarith

end NLA.MI24

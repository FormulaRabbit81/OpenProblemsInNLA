/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain the original
question; Matthew J. Colbrook retains the complete coefficient-identity proof.

Coercivity of the actual log-partition potential on the zero-sum hyperplane.
The finite-product sup norm is controlled by a largest coordinate. A single
positive summand bounds each row partition, so no interval subdivision or
dimension-dependent numerical computation is needed. Both inequalities of
the kernel-mode LeanCert half certificate enter the final estimate.
-/
import NLA.NM04.AnalyticBasics
import NLA.NM04.Numerical
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators

/-- Any upper bound for a zero-sum vector is nonnegative and controls its
sup norm. The deficits `q - t j` avoid a separate argument with erased sums. -/
theorem zero_mean_upper_bound_controls_norm {n : ℕ} (hn : 1 ≤ n)
    (t : Fin n → ℝ) (ht : t ∈ meanZero n) (q : ℝ)
    (hupper : ∀ j, t j ≤ q) : 0 ≤ q ∧ ‖t‖ ≤ (n : ℝ) * q := by
  have hsum : ∑ j, t j = 0 := ht
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn_one
  have htotal : 0 ≤ (n : ℝ) * q := by
    calc
      0 = ∑ j, t j := hsum.symm
      _ ≤ ∑ _j : Fin n, q := Finset.sum_le_sum fun j _ => hupper j
      _ = (n : ℝ) * q := by simp [nsmul_eq_mul]
  have hq : 0 ≤ q := nonneg_of_mul_nonneg_right htotal hn_pos
  refine ⟨hq, (pi_norm_le_iff_of_nonneg htotal).mpr ?_⟩
  intro j
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hdeficit : q - t j ≤ (n : ℝ) * q := by
      calc
        q - t j ≤ ∑ k : Fin n, (q - t k) :=
          Finset.single_le_sum (fun k _ => sub_nonneg.mpr (hupper k))
            (Finset.mem_univ j)
        _ = (n : ℝ) * q := by
          simp [Finset.sum_sub_distrib, hsum, nsmul_eq_mul]
    linarith only [hdeficit, hq]
  · exact (hupper j).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hn_one hq)

/-- One summand of a positive row partition supplies a logarithmic lower
bound. No approximation to `exp` or `log` is used. -/
theorem log_row_partition_lower_bound {m n : ℕ}
    (A : Rect m n) (a : ℝ) (ha : 0 < a) (haA : ∀ i j, a ≤ A i j)
    (t : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    Real.log a + t j ≤ Real.log (rowPartition A t i) := by
  have hterm : a * Real.exp (t j) ≤ rowPartition A t i := by
    calc
      a * Real.exp (t j) ≤ A i j * Real.exp (t j) :=
        mul_le_mul_of_nonneg_right (haA i j) (Real.exp_pos (t j)).le
      _ ≤ rowPartition A t i := by
        unfold rowPartition
        exact Finset.single_le_sum
          (fun k _ => mul_nonneg (ha.le.trans (haA i k)) (Real.exp_pos (t k)).le)
          (Finset.mem_univ j)
  have hlog := Real.log_le_log (mul_pos ha (Real.exp_pos (t j))) hterm
  simpa only [Real.log_mul ha.ne' (Real.exp_pos (t j)).ne', Real.log_exp] using hlog

/-- On the zero-sum hyperplane the linear part of the potential vanishes,
and the same coordinate lower bound can be summed over every row. -/
theorem potential_lower_bound_at_coordinate {m n : ℕ}
    (A : Rect m n) (a : ℝ) (ha : 0 < a) (haA : ∀ i j, a ≤ A i j)
    (t : Fin n → ℝ) (ht : t ∈ meanZero n) (j : Fin n) :
    (m : ℝ) * Real.log a + (m : ℝ) * t j ≤ potential A t := by
  have hsum : ∑ k, t k = 0 := ht
  calc
    (m : ℝ) * Real.log a + (m : ℝ) * t j =
        ∑ _i : Fin m, (Real.log a + t j) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i, Real.log (rowPartition A t i) :=
      Finset.sum_le_sum fun i _ => log_row_partition_lower_bound A a ha haA t i j
    _ = potential A t := by simp [potential, hsum]

/-- The frozen coercivity contract, for all row counts including zero.
The positive half bound licenses multiplication of the sup-norm estimate;
the upper half bound weakens the resulting largest-coordinate estimate. -/
theorem zero_mean_coercivity {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (a : ℝ) (ha : 0 < a)
    (haA : ∀ i j, a ≤ A i j) (t : Fin n → ℝ) (ht : t ∈ meanZero n) :
    (1 / 2 : ℝ) * ((m : ℝ) / (n : ℝ)) * ‖t‖ + (m : ℝ) * Real.log a ≤
      potential A t := by
  classical
  obtain ⟨j, _hj, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) t
      ⟨firstIndex hn, Finset.mem_univ _⟩
  obtain ⟨htj, hnorm⟩ := zero_mean_upper_bound_controls_norm hn t ht (t j)
    (fun k => hmax k (Finset.mem_univ k))
  obtain ⟨hhalf_pos, hhalf_lt⟩ := coercivity_half_certificate
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    zero_lt_one.trans_le (Nat.one_le_cast.mpr hn)
  have hratio : 0 ≤ (m : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg m) hn_pos.le
  have hnorm_half : (1 / 2 : ℝ) * ((m : ℝ) / (n : ℝ)) * ‖t‖ ≤
      (m : ℝ) * t j := by
    calc
      (1 / 2 : ℝ) * ((m : ℝ) / (n : ℝ)) * ‖t‖ ≤
          (1 / 2 : ℝ) * ((m : ℝ) / (n : ℝ)) * ((n : ℝ) * t j) :=
        mul_le_mul_of_nonneg_left hnorm (mul_nonneg hhalf_pos.le hratio)
      _ = (1 / 2 : ℝ) * ((((m : ℝ) / (n : ℝ)) * (n : ℝ)) * t j) := by ring
      _ = (1 / 2 : ℝ) * ((m : ℝ) * t j) := by
        rw [div_mul_cancel₀ _ hn_pos.ne']
      _ ≤ (m : ℝ) * t j := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hhalf_lt.le (mul_nonneg (Nat.cast_nonneg m) htj)
  calc
    (1 / 2 : ℝ) * ((m : ℝ) / (n : ℝ)) * ‖t‖ + (m : ℝ) * Real.log a ≤
        (m : ℝ) * t j + (m : ℝ) * Real.log a := add_le_add hnorm_half le_rfl
    _ = (m : ℝ) * Real.log a + (m : ℝ) * t j := add_comm _ _
    _ ≤ potential A t := potential_lower_bound_at_coordinate A a ha haA t ht j

#print axioms zero_mean_coercivity
#assert_trust kernel zero_mean_coercivity

end
end NLA.NM04

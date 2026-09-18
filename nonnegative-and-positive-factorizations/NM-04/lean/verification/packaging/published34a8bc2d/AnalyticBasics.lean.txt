/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Rowland and Wu retain the original
question; Matthew J. Colbrook retains the complete coefficient-identity proof.

Elementary analytic prerequisites for the actual positive rectangular
scaling. The derivative is derived from finite sums and Mathlib's proved
exp/log chain rules, then rearranged into the frozen column-imbalance form.
-/
import NLA.NM04.Definitions
import LeanCert.Tactic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.NM04
noncomputable section
open scoped BigOperators

theorem row_partition_positive {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (t : Fin n → ℝ) (i : Fin m) :
    0 < rowPartition A t i := by
  unfold rowPartition
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (hA i j) (Real.exp_pos (t j))
  · exact ⟨firstIndex hn, Finset.mem_univ _⟩

/-- Positivity is unnecessary for continuity of a row's finite exponential sum. -/
theorem rowPartition_continuous {m n : ℕ} (A : Rect m n) (i : Fin m) :
    Continuous (fun t : Fin n → ℝ => rowPartition A t i) := by
  unfold rowPartition
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul (Real.continuous_exp.comp (continuous_apply j))

theorem potential_continuous {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) : Continuous (potential A) := by
  unfold potential
  apply Continuous.sub
  · exact continuous_finsetSum _ fun i _ =>
      (rowPartition_continuous A i).log
        (fun t => (row_partition_positive hn A hA t i).ne')
  · exact continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_apply j)

/-- The chain rule applies before positivity is needed for the later logarithm. -/
theorem rowPartition_line_derivative {m n : ℕ} (A : Rect m n)
    (t d : Fin n → ℝ) (i : Fin m) :
    HasDerivAt (fun s : ℝ => rowPartition A (t + s • d) i)
      (∑ j, A i j * Real.exp (t j) * d j) 0 := by
  unfold rowPartition
  apply HasDerivAt.fun_sum
  intro j _
  have hj : HasDerivAt (fun s : ℝ => t j + s * d j) (d j) 0 :=
    (hasDerivAt_mul_const (x := (0 : ℝ)) (d j)).const_add (t j)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero,
    mul_assoc] using hj.exp.const_mul (A i j)

/-- Reorder the finite derivative sum into column imbalance. No denominator
    cancellation or nonzero hypothesis is needed for this algebraic identity. -/
theorem potential_directional_rearrangement {m n : ℕ} (A : Rect m n)
    (t d : Fin n → ℝ) :
    (∑ i, (∑ j, A i j * Real.exp (t j) * d j) / rowPartition A t i) -
        ((m : ℝ) / (n : ℝ)) * (∑ j, d j) =
      ∑ j, d j * columnImbalance A t j := by
  simp only [columnImbalance, mul_sub, Finset.sum_sub_distrib, Finset.sum_div,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

/-- The displayed data must be the actual derivative along every real line. -/
theorem potential_line_derivative {m n : ℕ} (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (t d : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => potential A (t + s • d))
      (∑ j, d j * columnImbalance A t j) 0 := by
  have hlogs :
      HasDerivAt (fun s : ℝ => ∑ i, Real.log (rowPartition A (t + s • d) i))
        (∑ i, (∑ j, A i j * Real.exp (t j) * d j) / rowPartition A t i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hne : rowPartition A (t + (0 : ℝ) • d) i ≠ 0 := by
      simpa only [zero_smul, add_zero] using
        (row_partition_positive hn A hA t i).ne'
    simpa only [zero_smul, add_zero] using
      (rowPartition_line_derivative A t d i).log hne
  have hsum : HasDerivAt (fun s : ℝ => ∑ j, (t + s • d) j) (∑ j, d j) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      (hasDerivAt_mul_const (x := (0 : ℝ)) (d j)).const_add (t j)
  have hderiv :
      HasDerivAt (fun s : ℝ => potential A (t + s • d))
        ((∑ i, (∑ j, A i j * Real.exp (t j) * d j) / rowPartition A t i) -
          ((m : ℝ) / (n : ℝ)) * (∑ j, d j)) 0 := by
    simpa only [potential] using hlogs.fun_sub (hsum.const_mul ((m : ℝ) / (n : ℝ)))
  simpa only [potential_directional_rearrangement] using hderiv

#print axioms row_partition_positive
#assert_trust kernel row_partition_positive
#print axioms potential_continuous
#assert_trust kernel potential_continuous
#print axioms potential_line_derivative
#assert_trust kernel potential_line_derivative

end
end NLA.NM04

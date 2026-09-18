/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A half-sized block and a uniform bound imply exponential decay for an actual
nonnegative submultiplicative sequence. A symbolic N-th root suffices. The
remainder costs only a factor two, eliminating a finite maximization over
lengths and any numerical root evaluation or dimension-dependent computation.
-/
import NLA.MF07.MatrixBasics

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06

lemma exponential_decay_of_half_block (g : ℕ → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (hg0 : ∀ n : ℕ, 0 ≤ g n) (hgzero : g 0 ≤ 1)
    (hgsub : ∀ m n : ℕ, g (m + n) ≤ g m * g n)
    (hbound : ∀ n : ℕ, g n ≤ K) (N : ℕ) (hN : 1 ≤ N) (hsmall : g N ≤ 1 / 2) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ n : ℕ, g n ≤ (2 * K) * q ^ n := by
  let q : ℝ := (1 / 2 : ℝ) ^ ((N : ℝ)⁻¹)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (inv_pos.mpr hNpos)
  have hqN : q ^ N = 1 / 2 := Real.rpow_inv_natCast_pow (by norm_num) (by omega)
  have hblock : g N ≤ q ^ N := by rw [hqN]; exact hsmall
  have hblocks : ∀ k : ℕ, g (k * N) ≤ (q ^ N) ^ k := by
    intro k
    induction k with
    | zero => simpa only [Nat.zero_mul, pow_zero] using hgzero
    | succ k ih =>
        rw [Nat.succ_mul, pow_succ]
        exact (hgsub (k * N) N).trans
          (mul_le_mul ih hblock (hg0 N) (pow_nonneg (pow_nonneg hq0.le N) k))
  refine ⟨q, hq0, hq1, ?_⟩
  intro n
  have hdecomp : n = (n / N) * N + n % N := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod n N).symm
  have hblockn : g ((n / N) * N) ≤ q ^ ((n / N) * N) := by
    simpa only [← pow_mul, Nat.mul_comm] using hblocks (n / N)
  have hrem : (1 : ℝ) / 2 ≤ q ^ (n % N) := by
    rw [← hqN]
    exact pow_le_pow_of_le_one hq0.le hq1.le (Nat.mod_lt n (by omega)).le
  have hfirst : g n ≤ K * q ^ ((n / N) * N) := by
    calc
      g n = g ((n / N) * N + n % N) := congrArg g hdecomp
      _ ≤ g ((n / N) * N) * g (n % N) := hgsub _ _
      _ ≤ q ^ ((n / N) * N) * K :=
        mul_le_mul hblockn (hbound (n % N)) (hg0 (n % N)) (pow_nonneg hq0.le _)
      _ = K * q ^ ((n / N) * N) := mul_comm _ _
  have hremfactor : (1 : ℝ) ≤ 2 * q ^ (n % N) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hremfactor
    (mul_nonneg (zero_le_one.trans hK) (pow_nonneg hq0.le ((n / N) * N)))
  calc
    g n ≤ K * q ^ ((n / N) * N) := hfirst
    _ ≤ (K * q ^ ((n / N) * N)) * (2 * q ^ (n % N)) := by
      simpa only [mul_one] using hscale
    _ = (2 * K) * (q ^ ((n / N) * N) * q ^ (n % N)) := by ring
    _ = (2 * K) * q ^ ((n / N) * N + n % N) := by rw [pow_add]
    _ = (2 * K) * q ^ n := by rw [← hdecomp]

#print axioms exponential_decay_of_half_block
#assert_trust kernel exponential_decay_of_half_block

end NLA.MF06

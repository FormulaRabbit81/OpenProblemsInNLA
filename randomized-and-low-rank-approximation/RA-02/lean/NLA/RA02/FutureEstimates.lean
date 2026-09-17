/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.RA02.RetainedCombinatorics

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma finite_sum_bound (r : ℕ) (U : Finset (Fin r)) (f : Fin r → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hf : ∀ i ∈ U, f i ≤ M) :
    ∑ i ∈ U, f i ≤ (r : ℝ) * M := by
  classical
  have hcard : (U.card : ℝ) ≤ r := by
    exact_mod_cast (show U.card ≤ r by simpa using U.card_le_univ)
  calc
    (∑ i ∈ U, f i) ≤ ∑ _i ∈ U, M := Finset.sum_le_sum hf
    _ = (U.card : ℝ) * M := by simp
    _ ≤ (r : ℝ) * M := mul_le_mul_of_nonneg_right hcard hM

lemma diagonalWeight_antitone (r : ℕ) (hr : 1 ≤ r) {i j : ℕ} (hij : i ≤ j) :
    diagonalWeight r j ≤ diagonalWeight r i := by
  rcases scalar_parameters r hr with ⟨ht0, ht1, he0, he2, ht2, hrest⟩
  exact pow_le_pow_of_le_one he0.le (he2.trans ht2.le) hij

lemma future_diagonal_sum_bound (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s < r) :
    ∑ i ∈ futureOrdinary r s, diagonalWeight r i.val ≤
      scaleParameter r ^ s * (1 + (r : ℝ) * smallParameter r ^ 2) := by
  classical
  let j : Fin r := ⟨s, hs⟩
  have hj : j ∈ futureOrdinary r s := (mem_futureOrdinary r s j).2 le_rfl
  have he := (scalar_parameters r hr).2.2.2.1
  have hsum := finite_sum_bound r ((futureOrdinary r s).erase j)
    (fun i => diagonalWeight r i.val) (scaleParameter r ^ s * smallParameter r ^ 2)
    (mul_nonneg (pow_nonneg (scaleParameter_pos r).le _) (sq_nonneg _)) (by
      intro i hi
      have hmem := (mem_futureOrdinary r s i).1 (Finset.mem_erase.mp hi).2
      have hne : i.val ≠ s := by
        intro heq
        apply (Finset.mem_erase.mp hi).1
        exact Fin.ext heq
      have hsi : s + 1 ≤ i.val := by omega
      calc
        diagonalWeight r i.val ≤ diagonalWeight r (s + 1) :=
          diagonalWeight_antitone r hr hsi
        _ = scaleParameter r ^ s * scaleParameter r := by rw [diagonalWeight, pow_succ]
        _ ≤ scaleParameter r ^ s * smallParameter r ^ 2 :=
          mul_le_mul_of_nonneg_left he (pow_nonneg (scaleParameter_pos r).le _))
  have hsplit := Finset.sum_erase_add (futureOrdinary r s)
    (fun i => diagonalWeight r i.val) hj
  have hjval : diagonalWeight r j.val = scaleParameter r ^ s := rfl
  rw [hjval] at hsplit
  nlinarith only [hsum, hsplit]

lemma future_weighted_sum_bound (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s < r) :
    ∑ i ∈ futureOrdinary r s, diagonalWeight r i.val * couplingWeight r i.val ^ 2 ≤
      (r : ℝ) * scaleParameter r ^ s * smallParameter r ^ 2 := by
  have ht0 := smallParameter_pos r
  have ht1 := (smallParameter_lt_one r hr).le
  have hsum := finite_sum_bound r (futureOrdinary r s)
    (fun i => diagonalWeight r i.val * couplingWeight r i.val ^ 2)
    (scaleParameter r ^ s * smallParameter r ^ 2)
    (mul_nonneg (pow_nonneg (scaleParameter_pos r).le _) (sq_nonneg _)) (by
      intro i hi
      have hd := diagonalWeight_antitone r hr ((mem_futureOrdinary r s i).1 hi)
      have ha : couplingWeight r i.val ^ 2 ≤ smallParameter r ^ 2 := by
        rw [couplingWeight, ← pow_mul]
        exact pow_le_pow_of_le_one ht0.le ht1 (by omega)
      exact mul_le_mul hd ha (sq_nonneg _) (pow_nonneg (scaleParameter_pos r).le _))
  simpa only [mul_assoc] using hsum

lemma epsilon_remainder_bound (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s < r) :
    scaleParameter r ^ r ≤ scaleParameter r ^ s * smallParameter r ^ 2 := by
  have he := (scalar_parameters r hr).2.2.2.1
  calc
    scaleParameter r ^ r ≤ scaleParameter r ^ (s + 1) :=
      diagonalWeight_antitone r hr (by omega)
    _ = scaleParameter r ^ s * scaleParameter r := pow_succ _ _
    _ ≤ scaleParameter r ^ s * smallParameter r ^ 2 :=
      mul_le_mul_of_nonneg_left he (pow_nonneg (scaleParameter_pos r).le _)

lemma scale_le_coupling_square (r : ℕ) (hr : 1 ≤ r) (j : Fin r) :
    scaleParameter r ≤ smallParameter r ^ 2 * couplingWeight r j.val ^ 2 := by
  have ht0 := smallParameter_pos r
  have ht1 := (smallParameter_lt_one r hr).le
  calc
    scaleParameter r ≤ smallParameter r ^ (2 + (j.val + 1) * 2) :=
      pow_le_pow_of_le_one ht0.le ht1 (by have hj := j.isLt; omega)
    _ = smallParameter r ^ 2 * couplingWeight r j.val ^ 2 := by
      rw [pow_add, pow_mul, couplingWeight]

lemma exceptional_remainder_bound (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s < r)
    (j : Fin r) :
    scaleParameter r ^ r / couplingWeight r j.val ^ 2 ≤
      scaleParameter r ^ s * smallParameter r ^ 2 := by
  have ha : 0 < couplingWeight r j.val ^ 2 := pow_pos (couplingWeight_pos r j.val) _
  apply (div_le_iff₀ ha).2
  have he : scaleParameter r ^ r ≤ scaleParameter r ^ s * scaleParameter r := by
    simpa only [diagonalWeight, pow_succ] using (diagonalWeight_antitone r hr (show s + 1 ≤ r by omega))
  calc
    scaleParameter r ^ r ≤ scaleParameter r ^ s * scaleParameter r := he
    _ ≤ scaleParameter r ^ s * (smallParameter r ^ 2 * couplingWeight r j.val ^ 2) :=
      mul_le_mul_of_nonneg_left (scale_le_coupling_square r hr j)
        (pow_nonneg (scaleParameter_pos r).le _)
    _ = _ := by ring

lemma later_coupling_ratio_bound (r : ℕ) (hr : 1 ≤ r) (j i : Fin r)
    (hji : j.val < i.val) :
    couplingWeight r i.val ^ 2 ≤ smallParameter r ^ 2 * couplingWeight r j.val ^ 2 := by
  have ht0 := smallParameter_pos r
  have ht1 := (smallParameter_lt_one r hr).le
  calc
    couplingWeight r i.val ^ 2 ≤ smallParameter r ^ (2 + (j.val + 1) * 2) := by
      rw [couplingWeight, ← pow_mul]
      exact pow_le_pow_of_le_one ht0.le ht1 (by omega)
    _ = smallParameter r ^ 2 * couplingWeight r j.val ^ 2 := by
      rw [pow_add, pow_mul, couplingWeight]

lemma future_weighted_ratio_sum_bound (r : ℕ) (hr : 1 ≤ r) (s : ℕ) (hs : s < r)
    (j : Fin r) (hj : j.val < s) :
    ∑ i ∈ futureOrdinary r s,
        diagonalWeight r i.val * couplingWeight r i.val ^ 2 / couplingWeight r j.val ^ 2 ≤
      (r : ℝ) * scaleParameter r ^ s * smallParameter r ^ 2 := by
  have ha : 0 < couplingWeight r j.val ^ 2 := pow_pos (couplingWeight_pos r j.val) _
  have hsum := finite_sum_bound r (futureOrdinary r s)
    (fun i => diagonalWeight r i.val * couplingWeight r i.val ^ 2 /
      couplingWeight r j.val ^ 2)
    (scaleParameter r ^ s * smallParameter r ^ 2)
    (mul_nonneg (pow_nonneg (scaleParameter_pos r).le _) (sq_nonneg _)) (by
      intro i hi
      have hsi := (mem_futureOrdinary r s i).1 hi
      have hd := diagonalWeight_antitone r hr hsi
      have hc := later_coupling_ratio_bound r hr j i (by omega)
      apply (div_le_iff₀ ha).2
      calc
        diagonalWeight r i.val * couplingWeight r i.val ^ 2 ≤
            scaleParameter r ^ s * (smallParameter r ^ 2 * couplingWeight r j.val ^ 2) :=
          mul_le_mul hd hc (sq_nonneg _) (pow_nonneg (scaleParameter_pos r).le _)
        _ = _ := by ring)
  simpa only [mul_assoc] using hsum

lemma trace_budget_scalar_bound (r : ℕ) (hr : 1 ≤ r) :
    1 + (2 * (r : ℝ) + 1) * smallParameter r ^ 2 ≤ 1 + 1 / (r : ℝ) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hden : 0 < 2 * (r : ℝ) + 1 := by positivity
  have heq : (2 * (r : ℝ) + 1) * smallParameter r ^ 2 =
      1 / (2 * (r : ℝ) + 1) := by
    unfold smallParameter
    field_simp [hden.ne'] <;> ring
  rw [heq]
  exact add_le_add le_rfl (one_div_le_one_div_of_le hr0 (by linarith))

#print axioms future_diagonal_sum_bound
#assert_trust kernel future_diagonal_sum_bound
#print axioms future_weighted_ratio_sum_bound
#assert_trust kernel future_weighted_ratio_sum_bound
#print axioms trace_budget_scalar_bound
#assert_trust kernel trace_budget_scalar_bound

end
end NLA.RA02

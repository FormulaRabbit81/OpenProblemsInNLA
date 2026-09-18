/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Each transition weight uses a suffix in the first diagonal block and a prefix
in the second. Splitting two transition times exposes the SAME middle word.
Grouping the adjacent endpoint factors keeps the separation constant at K^4
rather than K^6. The existing scalar theorem then bounds every finite sum.
-/
import NLA.MF06.PairedWords
import NLA.MF06.SeparatedSum
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma wordIn_take {d : ℕ} (M : Set (Square d)) (w : List (Square d))
    (hw : WordIn M w) (i : ℕ) : WordIn M (w.take i) :=
  fun A hA => hw A (List.mem_of_mem_take hA)

lemma wordIn_drop {d : ℕ} (M : Set (Square d)) (w : List (Square d))
    (hw : WordIn M w) (i : ℕ) : WordIn M (w.drop i) :=
  fun A hA => hw A (List.mem_of_mem_drop hA)

def transitionWeight {d m n : ℕ} (f : Square d → Square m) (g : Square d → Square n)
    (w : List (Square d)) (i : ℕ) : ℝ :=
  spectralNorm (matrixProduct ((w.drop (i + 1)).map f)) *
    spectralNorm (matrixProduct ((w.take i).map g))

lemma transitionWeight_nonneg {d m n : ℕ} (f : Square d → Square m)
    (g : Square d → Square n) (w : List (Square d)) (i : ℕ) :
    0 ≤ transitionWeight f g w i := mul_nonneg (spectralNorm_nonneg _) (spectralNorm_nonneg _)

lemma transitionWeight_le {d m n : ℕ} (M : Set (Square d))
    (f : Square d → Square m) (g : Square d → Square n) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map f)) ≤ K)
    (hg : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map g)) ≤ K)
    (w : List (Square d)) (hw : WordIn M w) (i : ℕ) : transitionWeight f g w i ≤ K ^ 2 := by
  have h := mul_le_mul (hf _ (wordIn_drop M w hw (i + 1)))
    (hg _ (wordIn_take M w hw i)) (spectralNorm_nonneg _) hK
  simpa only [transitionWeight, pow_two] using h

/-- The middle segment is the same original list for both diagonal maps.
The estimate remains valid if that segment is empty. -/
lemma transition_pair_middle_bound {d m n : ℕ} (M : Set (Square d))
    (f : Square d → Square m) (g : Square d → Square n) (K F q : ℝ) (hK : 0 ≤ K)
    (hf : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map f)) ≤ K)
    (hg : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map g)) ≤ K)
    (hpair : ∀ w, WordIn M w →
      spectralNorm (matrixProduct (w.map f)) * spectralNorm (matrixProduct (w.map g)) ≤
        F * q ^ w.length)
    (w : List (Square d)) (hw : WordIn M w) (i j : ℕ) (hij : i < j) (hj : j ≤ w.length) :
    transitionWeight f g w i * transitionWeight f g w j ≤ K ^ 4 * F * q ^ (j - i - 1) := by
  let v : List (Square d) := (w.drop (i + 1)).take (j - i - 1)
  have hv : WordIn M v := wordIn_take M (w.drop (i + 1)) (wordIn_drop M w hw (i + 1)) _
  have hvlength : v.length = j - i - 1 := by
    dsimp only [v]
    simp only [List.length_take, List.length_drop]
    omega
  have hindex : (i + 1) + (j - i - 1) = j := by omega
  have hdrop : w.drop (i + 1) = v ++ w.drop j := by
    simpa only [hindex] using (List.drop_take_append_drop w (i + 1) (j - i - 1)).symm
  have htake : w.take j = w.take (i + 1) ++ v := by
    simpa only [hindex] using (List.take_add (l := w) (i := i + 1) (j := j - i - 1))
  have hi : transitionWeight f g w i ≤ K ^ 2 * spectralNorm (matrixProduct (v.map f)) := by
    unfold transitionWeight
    rw [hdrop, List.map_append, matrixProduct_append]
    calc
      spectralNorm (matrixProduct ((w.drop j).map f) * matrixProduct (v.map f)) *
          spectralNorm (matrixProduct ((w.take i).map g)) ≤
          (spectralNorm (matrixProduct ((w.drop j).map f)) * spectralNorm (matrixProduct (v.map f))) *
            spectralNorm (matrixProduct ((w.take i).map g)) :=
        mul_le_mul_of_nonneg_right (spectralNorm_mul_le _ _) (spectralNorm_nonneg _)
      _ ≤ (K * spectralNorm (matrixProduct (v.map f))) * K :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (hf _ (wordIn_drop M w hw j)) (spectralNorm_nonneg _))
          (hg _ (wordIn_take M w hw i)) (spectralNorm_nonneg _)
          (mul_nonneg hK (spectralNorm_nonneg _))
      _ = K ^ 2 * spectralNorm (matrixProduct (v.map f)) := by ring
  have hjbound : transitionWeight f g w j ≤ K ^ 2 * spectralNorm (matrixProduct (v.map g)) := by
    unfold transitionWeight
    rw [htake, List.map_append, matrixProduct_append]
    have hright : spectralNorm (matrixProduct (v.map g) * matrixProduct ((w.take (i + 1)).map g)) ≤
        spectralNorm (matrixProduct (v.map g)) * K :=
      (spectralNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hg _ (wordIn_take M w hw (i + 1))) (spectralNorm_nonneg _))
    calc
      spectralNorm (matrixProduct ((w.drop (j + 1)).map f)) *
          spectralNorm (matrixProduct (v.map g) * matrixProduct ((w.take (i + 1)).map g)) ≤
          K * (spectralNorm (matrixProduct (v.map g)) * K) :=
        mul_le_mul (hf _ (wordIn_drop M w hw (j + 1))) hright (spectralNorm_nonneg _) hK
      _ = K ^ 2 * spectralNorm (matrixProduct (v.map g)) := by ring
  calc
    transitionWeight f g w i * transitionWeight f g w j ≤
        (K ^ 2 * spectralNorm (matrixProduct (v.map f))) *
          (K ^ 2 * spectralNorm (matrixProduct (v.map g))) :=
      mul_le_mul hi hjbound (transitionWeight_nonneg f g w j)
        (mul_nonneg (pow_nonneg hK _) (spectralNorm_nonneg _))
    _ = K ^ 4 * (spectralNorm (matrixProduct (v.map f)) * spectralNorm (matrixProduct (v.map g))) :=
      by ring
    _ ≤ K ^ 4 * (F * q ^ v.length) := mul_le_mul_of_nonneg_left (hpair v hv) (pow_nonneg hK _)
    _ = K ^ 4 * F * q ^ (j - i - 1) := by rw [hvlength]; ring

/-- Uniform transition sum for all lengths, including zero. -/
lemma transition_sum_bound {d m n : ℕ} (M : Set (Square d))
    (f : Square d → Square m) (g : Square d → Square n) (K F q : ℝ)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hq : 0 < q) (hq1 : q < 1)
    (hf : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map f)) ≤ K)
    (hg : ∀ w, WordIn M w → spectralNorm (matrixProduct (w.map g)) ≤ K)
    (hpair : ∀ w, WordIn M w →
      spectralNorm (matrixProduct (w.map f)) * spectralNorm (matrixProduct (w.map g)) ≤
        F * q ^ w.length)
    (w : List (Square d)) (hw : WordIn M w) :
    (∑ i : Fin w.length, transitionWeight f g w i.val) ≤
      2 * K ^ 2 + 4 * (((K ^ 4 * F / q) * q) / (1 - q) ^ 2) + 1 := by
  have hshift (k : ℕ) : K ^ 4 * F * q ^ k = (K ^ 4 * F / q) * q ^ (k + 1) := by
    rw [pow_succ' q k, ← mul_assoc, div_mul_cancel₀ _ hq.ne']
  have hordered (i j : Fin w.length) (hij : i < j) :
      transitionWeight f g w i.val * transitionWeight f g w j.val ≤
        (K ^ 4 * F / q) * q ^ (j.val - i.val) := by
    have hlt := Fin.lt_def.mp hij
    have hraw := transition_pair_middle_bound M f g K F q hK hf hg hpair w hw
      i.val j.val hlt j.isLt.le
    have hs := hshift (j.val - i.val - 1)
    rw [show j.val - i.val - 1 + 1 = j.val - i.val by omega] at hs
    exact hraw.trans_eq hs
  apply separated_sum_bound w.length (fun i => transitionWeight f g w i.val)
    (K ^ 2) (K ^ 4 * F / q) q (pow_nonneg hK _)
    (div_nonneg (mul_nonneg (pow_nonneg hK _) hF) hq.le) hq hq1
    (fun i => transitionWeight_nonneg f g w i.val)
    (fun i => transitionWeight_le M f g K hK hf hg w hw i.val)
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · simpa only [max_eq_right (Fin.le_def.mp hij.le), min_eq_left (Fin.le_def.mp hij.le)] using
      hordered i j hij
  · have h := hordered j i hji
    simpa only [mul_comm (transitionWeight f g w j.val),
      max_eq_left (Fin.le_def.mp hji.le), min_eq_right (Fin.le_def.mp hji.le)] using h

#print axioms transition_sum_bound
#assert_trust kernel transition_sum_bound

end NLA.MF06

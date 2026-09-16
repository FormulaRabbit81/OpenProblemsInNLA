/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.Certificates
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace NLA.SP04

theorem scalar_admissible_bounds {s : Fin 3 → ℝ} (hs : Admissible s) (i : Fin 3) :
    7/4 < s i ∧ s i < 44/25 := by
  rcases hs with ⟨h0, h01, h12, h2⟩
  fin_cases i
  · change 7/4 < s 0 ∧ s 0 < 44/25
    exact ⟨h0, (h01.trans h12).trans h2⟩
  · change 7/4 < s 1 ∧ s 1 < 44/25
    exact ⟨h0.trans h01, h12.trans h2⟩
  · change 7/4 < s 2 ∧ s 2 < 44/25
    exact ⟨(h0.trans h01).trans h12, h2⟩

theorem scalar_admissible_pos {s : Fin 3 → ℝ} (hs : Admissible s) (i : Fin 3) : 0 < s i := by
  have := (scalar_admissible_bounds hs i).1
  linarith

theorem negative_roots (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    0 < positiveRoot s t ∧ 0 ≤ negativeMagnitude s t ∧
    positiveRoot s t - negativeMagnitude s t = s ∧
    positiveRoot s t * negativeMagnitude s t = t := by
  have hd : 0 ≤ s^2 + 4*t := by positivity
  have hsq := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg (s^2 + 4*t)
  have hb : s ≤ Real.sqrt (s^2 + 4*t) := Real.le_sqrt_of_sq_le (by linarith)
  dsimp [positiveRoot, negativeMagnitude]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · ring
  · nlinarith

theorem negativeMagnitude_pos (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 < negativeMagnitude s t := by
  have h := negative_roots s t hs ht.le
  have : negativeMagnitude s t ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h
    linarith [h.2.2.2]
  exact lt_of_le_of_ne h.2.1 (Ne.symm this)

theorem negative_quadratic_roots (s t x : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    x^2 - s*x - t = 0 ↔ x = positiveRoot s t ∨ x = -negativeMagnitude s t := by
  have h := negative_roots s t hs ht
  have heq : (x-positiveRoot s t)*(x+negativeMagnitude s t) = x^2-s*x-t := by
    linear_combination -x * h.2.2.1 - h.2.2.2
  rw [← heq, mul_eq_zero]
  constructor
  · rintro (ha | hb)
    · exact Or.inl (sub_eq_zero.mp ha)
    · exact Or.inr (eq_neg_of_add_eq_zero_left hb)
  · rintro (rfl | rfl) <;> simp

theorem positiveRoot_continuous (s : ℝ) : Continuous (positiveRoot s) := by
  unfold positiveRoot
  fun_prop

theorem negativeMagnitude_continuous (s : ℝ) : Continuous (negativeMagnitude s) := by
  unfold negativeMagnitude
  fun_prop

theorem negative_roots_parameter_strict (s u v : ℝ) (hs : 0 < s)
    (hu : 0 ≤ u) (huv : u < v) :
    positiveRoot s u < positiveRoot s v ∧ negativeMagnitude s u < negativeMagnitude s v := by
  have hd : 0 ≤ s^2+4*u := by positivity
  have h := Real.sqrt_lt_sqrt hd (show s^2+4*u < s^2+4*v by linarith)
  dsimp [positiveRoot, negativeMagnitude]
  constructor <;> linarith

theorem negative_roots_order (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t) :
    positiveRoot a t < positiveRoot b t ∧ negativeMagnitude b t < negativeMagnitude a t := by
  have hb : 0 < b := ha.trans hab
  have h := negative_roots a t ha ht.le
  have k := negative_roots b t hb ht.le
  have hd : 0 ≤ a^2+4*t := by positivity
  have hsq := Real.sqrt_lt_sqrt hd (show a^2+4*t < b^2+4*t by nlinarith)
  have hp : positiveRoot a t < positiveRoot b t := by
    dsimp [positiveRoot]
    linarith
  refine ⟨hp, ?_⟩
  have hbp := negativeMagnitude_pos a t ha ht
  have hkp := negativeMagnitude_pos b t hb ht
  by_contra hn
  have hle : negativeMagnitude a t ≤ negativeMagnitude b t := le_of_not_gt hn
  have hm := mul_lt_mul hp hle hbp k.1.le
  linarith [h.2.2.2, k.2.2.2]

def selectedProduct (s : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  negativeMagnitude (s 0) t * positiveRoot (s 1) t * positiveRoot (s 2) t

theorem selectedProduct_continuous (s : Fin 3 → ℝ) : Continuous (selectedProduct s) := by
  exact ((negativeMagnitude_continuous (s 0)).mul
    (positiveRoot_continuous (s 1))).mul (positiveRoot_continuous (s 2))

theorem selectedProduct_strict {s : Fin 3 → ℝ} (hs : Admissible s) :
    StrictMonoOn (selectedProduct s) (Set.Ici 0) := by
  intro u hu v hv huv
  have h0 := negative_roots_parameter_strict (s 0) u v (scalar_admissible_pos hs 0) hu huv
  have h1 := negative_roots_parameter_strict (s 1) u v (scalar_admissible_pos hs 1) hu huv
  have h2 := negative_roots_parameter_strict (s 2) u v (scalar_admissible_pos hs 2) hu huv
  have r0 := negative_roots (s 0) v (scalar_admissible_pos hs 0) hv
  have r1 := negative_roots (s 1) u (scalar_admissible_pos hs 1) hu
  have r2 := negative_roots (s 2) u (scalar_admissible_pos hs 2) hu
  have v1 := negative_roots (s 1) v (scalar_admissible_pos hs 1) hv
  have hm := mul_lt_mul h0.2 h1.1.le r1.1 r0.2.1
  exact mul_lt_mul hm h2.1.le r2.1 (mul_nonneg r0.2.1 v1.1.le)

theorem selectedProduct_zero {s : Fin 3 → ℝ} (hs : Admissible s) :
    selectedProduct s 0 = 0 := by
  simp [selectedProduct, negativeMagnitude, Real.sqrt_sq (scalar_admissible_pos hs 0).le]

theorem selectedProduct_endpoint {s : Fin 3 → ℝ} (hs : Admissible s) :
    1 < selectedProduct s (13/25) := by
  have ha (i : Fin 3) : 2 < positiveRoot (s i) (13/25) := by
    have h := negative_roots (s i) (13/25) (scalar_admissible_pos hs i) (by norm_num)
    have hb := (scalar_admissible_bounds hs i).1
    have he : (positiveRoot (s i) (13/25))^2 - s i*positiveRoot (s i) (13/25) - 13/25 = 0 :=
      (negative_quadratic_roots (s i) (13/25) _ (scalar_admissible_pos hs i) (by norm_num)).mpr (Or.inl rfl)
    have hl : s i < positiveRoot (s i) (13/25) := by
      have := negativeMagnitude_pos (s i) (13/25) (scalar_admissible_pos hs i) (by norm_num)
      linarith [h.2.2.1]
    by_contra hn
    have hle : positiveRoot (s i) (13/25) ≤ 2 := le_of_not_gt hn
    nlinarith
  have hb : 1/4 < negativeMagnitude (s 0) (13/25) := by
    have h := negative_roots (s 0) (13/25) (scalar_admissible_pos hs 0) (by norm_num)
    have hn := (scalar_admissible_bounds hs 0).2
    have hc := scalar_numerical_bounds.2.2.2
    by_contra hnot
    have hle : negativeMagnitude (s 0) (13/25) ≤ 1/4 := le_of_not_gt hnot
    nlinarith [h.2.1, h.2.2.1, h.2.2.2]
  have h1 := mul_lt_mul hb (ha 1).le (by norm_num : (0:ℝ)<2)
    (negative_roots (s 0) (13/25) (scalar_admissible_pos hs 0) (by norm_num)).2.1
  have h2 := mul_lt_mul h1 (ha 2).le (by norm_num : (0:ℝ)<2)
    (mul_nonneg (negative_roots (s 0) (13/25) (scalar_admissible_pos hs 0) (by norm_num)).2.1
      (negative_roots (s 1) (13/25) (scalar_admissible_pos hs 1) (by norm_num)).1.le)
  norm_num [selectedProduct] at h2 ⊢
  exact h2

theorem selected_parameter_exists (s : Fin 3 → ℝ) (hs : Admissible s) :
    ∃ t : ℝ, 0 < t ∧ t < 13/25 ∧ selectedProduct s t = 1 := by
  have hg : (1:ℝ) ∈ Set.Ioo (selectedProduct s 0) (selectedProduct s (13/25)) := by
    rw [selectedProduct_zero hs]
    exact ⟨by norm_num, selectedProduct_endpoint hs⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Ioo (show (0:ℝ)≤13/25 by norm_num)
    (selectedProduct_continuous s).continuousOn hg
  exact ⟨t, ht.1, ht.2, he⟩

end NLA.SP04

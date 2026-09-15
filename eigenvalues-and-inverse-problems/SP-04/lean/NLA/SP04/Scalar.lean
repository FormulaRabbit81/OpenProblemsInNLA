/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.ScalarPositive

noncomputable section
open scoped BigOperators
namespace NLA.SP04

def ScalarStationary (s x : Fin 3 → ℝ) (c : ℝ) : Prop :=
  (∀ i, (x i)^2-s i*x i+c=0) ∧ |∏ i, x i|=1

theorem nonnegative_scalar_impossible (s : Fin 3 → ℝ) (hs : Admissible s)
    (x : Fin 3 → ℝ) (c : ℝ) (hc : 0≤c) (hC : c≤13/25) :
    ¬ScalarStationary s x c := by
  intro hx
  let a := fun i : Fin 3 => largeRoot (s i) c
  let b := fun i : Fin 3 => smallRoot (s i) c
  have ha (i : Fin 3) : 1<a i := (nonnegative_roots (s i) c
    (scalar_admissible_bounds hs i).1 (scalar_admissible_bounds hs i).2 hc hC).1
  have hap (i : Fin 3) : 0<a i := lt_trans (by norm_num) (ha i)
  have hb (i : Fin 3) : 0≤b i := (nonnegative_roots (s i) c
    (scalar_admissible_bounds hs i).1 (scalar_admissible_bounds hs i).2 hc hC).2.2.1
  have hba (i : Fin 3) : b i≤a i := (nonnegative_roots (s i) c
    (scalar_admissible_bounds hs i).1 (scalar_admissible_bounds hs i).2 hc hC).2.2.2.1.le
  have h01 := nonnegative_roots_order (s 0) (s 1) c hs.1 hs.2.1
    (scalar_admissible_bounds hs 1).2 hc hC
  have h02 := nonnegative_roots_order (s 0) (s 2) c hs.1
    (hs.2.1.trans hs.2.2.1) hs.2.2.2 hc hC
  have hab01 : a 0≤a 1 := h01.1.le
  have hab02 : a 0≤a 2 := h02.1.le
  have hbb10 : b 1≤b 0 := h01.2
  have hbb20 : b 2≤b 0 := h02.2
  have hsmall : b 0*a 1*a 2<1 := nonnegative_product_bound hs c hc hC
  have hlarge : 1<a 0*a 1*a 2 := by
    calc (1:ℝ) = 1*1*1 := by ring
         _ < a 0*a 1*a 2 := by gcongr <;> exact ha _
  have p001 : a 0*a 1*b 2≤b 0*a 1*a 2 := by
    calc a 0*a 1*b 2 = b 2*a 1*a 0 := by ring
         _ ≤ b 0*a 1*a 2 := mul_le_mul
          (mul_le_mul_of_nonneg_right hbb20 (hap 1).le) hab02 (hap 0).le
          (mul_nonneg (hb 0) (hap 1).le)
  have p010 : a 0*b 1*a 2≤b 0*a 1*a 2 := by
    calc a 0*b 1*a 2 = b 1*a 0*a 2 := by ring
         _ ≤ b 0*a 1*a 2 := mul_le_mul_of_nonneg_right
          (mul_le_mul hbb10 hab01 (hap 0).le (hb 0)) (hap 2).le
  have p011 : a 0*b 1*b 2≤b 0*a 1*a 2 :=
    (mul_le_mul_of_nonneg_left (hba 2) (mul_nonneg (hap 0).le (hb 1))).trans p010
  have p101 : b 0*a 1*b 2≤b 0*a 1*a 2 :=
    mul_le_mul_of_nonneg_left (hba 2) (mul_nonneg (hb 0) (hap 1).le)
  have p110 : b 0*b 1*a 2≤b 0*a 1*a 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hba 1) (hb 0)) (hap 2).le
  have p111 : b 0*b 1*b 2≤b 0*a 1*a 2 :=
    (mul_le_mul_of_nonneg_left (hba 2) (mul_nonneg (hb 0) (hb 1))).trans p110
  have hr (i : Fin 3) : x i=a i ∨ x i=b i :=
    (nonnegative_quadratic_roots (s i) c (x i) (scalar_admissible_bounds hs i).1
      (scalar_admissible_bounds hs i).2 hc hC).mp (hx.1 i)
  have hxp (i : Fin 3) : 0≤x i := (hr i).elim (fun h => h ▸ (hap i).le) (fun h => h ▸ hb i)
  have hp : x 0*x 1*x 2=1 := by
    have h := hx.2
    rw [Fin.prod_univ_three, abs_of_nonneg (mul_nonneg (mul_nonneg (hxp 0) (hxp 1)) (hxp 2))] at h
    exact h
  rcases hr 0 with h0|h0 <;> rcases hr 1 with h1|h1 <;> rcases hr 2 with h2|h2 <;>
    rw [h0,h1,h2] at hp <;> linarith

theorem negative_scalar_comparison (s : Fin 3 → ℝ) (hs : Admissible s)
    (x : Fin 3 → ℝ) (t : ℝ) (ht : 0<t) (hx : ScalarStationary s x (-t)) :
    1≤selectedProduct s t ∧ (selectedProduct s t≤1 → x=selectedEntries s t) := by
  let a := fun i : Fin 3 => positiveRoot (s i) t
  let b := fun i : Fin 3 => negativeMagnitude (s i) t
  have ha (i : Fin 3) : 0<a i := (negative_roots (s i) t (scalar_admissible_pos hs i) ht.le).1
  have hb (i : Fin 3) : 0<b i := negativeMagnitude_pos (s i) t (scalar_admissible_pos hs i) ht
  have hba (i : Fin 3) : b i<a i := by
    have hd := (negative_roots (s i) t (scalar_admissible_pos hs i) ht.le).2.2.1
    have hp := scalar_admissible_pos hs i
    change a i-b i=s i at hd
    linarith
  have hbig (i : Fin 3) : 1<a i := by
    have hd := (negative_roots (s i) t (scalar_admissible_pos hs i) ht.le).2.2.1
    have hp := (scalar_admissible_bounds hs i).1
    change a i-b i=s i at hd
    linarith [hb i]
  have h01 := negative_roots_order (s 0) (s 1) t (scalar_admissible_pos hs 0) hs.2.1 ht
  have h02 := negative_roots_order (s 0) (s 2) t (scalar_admissible_pos hs 0)
    (hs.2.1.trans hs.2.2.1) ht
  have hab01 : a 0<a 1 := h01.1
  have hab02 : a 0<a 2 := h02.1
  have hbb10 : b 1<b 0 := h01.2
  have hbb20 : b 2<b 0 := h02.2
  have hlarge : 1<a 0*a 1*a 2 := by
    calc (1:ℝ) = 1*1*1 := by ring
         _ < a 0*a 1*a 2 := by gcongr <;> exact hbig _
  have p001 : a 0*a 1*b 2<b 0*a 1*a 2 := by
    calc a 0*a 1*b 2 = b 2*a 1*a 0 := by ring
         _ < b 0*a 1*a 2 := mul_lt_mul
          (mul_lt_mul_of_pos_right hbb20 (ha 1)) hab02.le (ha 0)
          (mul_pos (hb 0) (ha 1)).le
  have p010 : a 0*b 1*a 2<b 0*a 1*a 2 := by
    calc a 0*b 1*a 2 = b 1*a 0*a 2 := by ring
         _ < b 0*a 1*a 2 := mul_lt_mul_of_pos_right
          (mul_lt_mul hbb10 hab01.le (ha 0) (hb 0).le) (ha 2)
  have p011 : a 0*b 1*b 2<b 0*a 1*a 2 :=
    (mul_le_mul_of_nonneg_left (hba 2).le (mul_pos (ha 0) (hb 1)).le).trans_lt p010
  have p101 : b 0*a 1*b 2<b 0*a 1*a 2 :=
    mul_lt_mul_of_pos_left (hba 2) (mul_pos (hb 0) (ha 1))
  have p110 : b 0*b 1*a 2<b 0*a 1*a 2 :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left (hba 1) (hb 0)) (ha 2)
  have p111 : b 0*b 1*b 2<b 0*a 1*a 2 :=
    (mul_le_mul_of_nonneg_left (hba 2).le (mul_pos (hb 0) (hb 1)).le).trans_lt p110
  have hr (i : Fin 3) : x i=a i ∨ x i= -b i :=
    (negative_quadratic_roots (s i) t (x i) (scalar_admissible_pos hs i) ht.le).mp
      (by simpa [sub_eq_add_neg] using hx.1 i)
  have hp : |x 0| * |x 1| * |x 2| = 1 := by simpa [Fin.prod_univ_three, abs_mul] using hx.2
  change 1≤b 0*a 1*a 2 ∧ (b 0*a 1*a 2≤1 → x=selectedEntries s t)
  rcases hr 0 with h0|h0 <;> rcases hr 1 with h1|h1 <;> rcases hr 2 with h2|h2 <;>
    simp only [h0,h1,h2,abs_neg,abs_of_pos (ha 0),abs_of_pos (ha 1),abs_of_pos (ha 2),
      abs_of_pos (hb 0),abs_of_pos (hb 1),abs_of_pos (hb 2)] at hp
  · linarith
  · exact ⟨by linarith, fun h => by exfalso; linarith⟩
  · exact ⟨by linarith, fun h => by exfalso; linarith⟩
  · exact ⟨by linarith, fun h => by exfalso; linarith⟩
  · refine ⟨hp.ge, fun _ => ?_⟩
    ext i
    fin_cases i
    · simpa [selectedEntries, b] using h0
    · simpa [selectedEntries, a] using h1
    · simpa [selectedEntries, a] using h2
  · exact ⟨by linarith, fun h => by exfalso; linarith⟩
  · exact ⟨by linarith, fun h => by exfalso; linarith⟩
  · exact ⟨by linarith, fun h => by exfalso; linarith⟩

theorem scalar_least_unique (s : Fin 3 → ℝ) (hs : Admissible s) (t : ℝ)
    (ht : 0<t) (hT : t<13/25) (hg : selectedProduct s t=1)
    (x : Fin 3 → ℝ) (c : ℝ) (hx : ScalarStationary s x c) :
    t≤|c| ∧ (t=|c| → x=selectedEntries s t ∧ c= -t) := by
  have hbound (hle : |c|≤t) : x=selectedEntries s t ∧ c= -t := by
    have hc : c<0 := by
      by_contra hn
      have hn : 0≤c := le_of_not_gt hn
      have hcle : c≤13/25 := (le_abs_self c).trans (hle.trans hT.le)
      exact nonnegative_scalar_impossible s hs x c hn hcle hx
    have hu : 0< -c := neg_pos.mpr hc
    have hcmp := negative_scalar_comparison s hs x (-c) hu (by simpa using hx)
    have hct : -c≤t := by simpa [abs_of_neg hc] using hle
    have he : -c=t := by
      by_contra hn
      have hlt : -c<t := lt_of_le_of_ne hct hn
      have hmono := selectedProduct_strict hs hu.le ht.le hlt
      linarith [hcmp.1]
    constructor
    · have h := hcmp.2 (by simpa [he, hg])
      simpa [he] using h
    · linarith
  constructor
  · by_contra hn
    have hl : |c|<t := lt_of_not_ge hn
    have h := hbound hl.le
    rw [h.2, abs_neg, abs_of_pos ht] at hl
    exact hl.false
  · intro he
    exact hbound he.ge

theorem selected_scalar_stationary (s : Fin 3 → ℝ) (hs : Admissible s) (t : ℝ)
    (ht : 0<t) (hg : selectedProduct s t=1) :
    ScalarStationary s (selectedEntries s t) (-t) := by
  constructor
  · intro i
    have hr := negative_quadratic_roots (s i) t (selectedEntries s t i) (scalar_admissible_pos hs i) ht.le
    apply (show (selectedEntries s t i)^2-s i*selectedEntries s t i-t=0 →
      (selectedEntries s t i)^2-s i*selectedEntries s t i+-t=0 by intro h; linarith)
    apply hr.mpr
    fin_cases i <;> simp [selectedEntries]
  · have h0 := negativeMagnitude_pos (s 0) t (scalar_admissible_pos hs 0) ht
    have h1 := (negative_roots (s 1) t (scalar_admissible_pos hs 1) ht.le).1
    have h2 := (negative_roots (s 2) t (scalar_admissible_pos hs 2) ht.le).1
    simpa [selectedEntries, Fin.prod_univ_three, abs_mul, abs_of_pos h0,
      abs_of_pos h1, abs_of_pos h2, selectedProduct] using hg

theorem improved_scalar_feasible (s : Fin 3 → ℝ) (hs : Admissible s) (t : ℝ)
    (ht : 0<t) (hg : selectedProduct s t=1) : |∏ i, improvedEntries s t i|=1 := by
  have h0 := negativeMagnitude_pos (s 0) t (scalar_admissible_pos hs 0) ht
  have h1 := (negative_roots (s 1) t (scalar_admissible_pos hs 1) ht.le).1
  have h2 := (negative_roots (s 2) t (scalar_admissible_pos hs 2) ht.le).1
  simpa [improvedEntries, Fin.prod_univ_three, abs_mul, abs_of_pos h0,
    abs_of_pos h1, abs_of_pos h2, selectedProduct] using hg

theorem scalar_distance_improves (s : Fin 3 → ℝ) (hs : Admissible s) (t : ℝ) (ht : 0<t) :
    (∑ i, (s i-improvedEntries s t i)^2) < ∑ i, (s i-selectedEntries s t i)^2 := by
  have hp := mul_pos (scalar_admissible_pos hs 0)
    (negativeMagnitude_pos (s 0) t (scalar_admissible_pos hs 0) ht)
  simp only [Fin.sum_univ_three, selectedEntries, improvedEntries, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  nlinarith

#assert_trust kernel scalar_least_unique
#assert_trust kernel selected_parameter_exists
#assert_trust kernel scalar_distance_improves
#print axioms scalar_least_unique
#print axioms selected_parameter_exists
#print axioms scalar_distance_improves

end NLA.SP04

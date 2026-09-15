/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.SP04.ScalarRoots

noncomputable section
open scoped BigOperators
namespace NLA.SP04

def smallRoot (s c : ℝ) : ℝ := (s-Real.sqrt (s^2-4*c))/2

theorem positive_discriminant (s c : ℝ) (hs : 7/4 < s) (hc : c ≤ 13/25) :
    (99/100)^2 < s^2-4*c ∧ 99/100 < Real.sqrt (s^2-4*c) := by
  have hnum := scalar_numerical_bounds.1
  have h : (99/100)^2 < s^2-4*c := by nlinarith
  exact ⟨h, (Real.lt_sqrt (by norm_num)).mpr h⟩

theorem nonnegative_roots (s c : ℝ) (hs : 7/4 < s) (hS : s < 44/25)
    (hc : 0 ≤ c) (hC : c ≤ 13/25) :
    1 < largeRoot s c ∧ largeRoot s c < 44/25 ∧
    0 ≤ smallRoot s c ∧ smallRoot s c < largeRoot s c ∧
    largeRoot s c + smallRoot s c = s ∧ largeRoot s c * smallRoot s c = c := by
  have hd := positive_discriminant s c hs hC
  have hrad : 0 ≤ s^2-4*c := by nlinarith [hd.1]
  have hsq := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (s^2-4*c)
  have hle : Real.sqrt (s^2-4*c) ≤ s := (Real.sqrt_le_iff).mpr ⟨by linarith, by linarith⟩
  dsimp [largeRoot, smallRoot]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [hd.2]
  · linarith
  · linarith
  · linarith [hd.2]
  · ring
  · nlinarith

theorem nonnegative_quadratic_roots (s c x : ℝ) (hs : 7/4 < s) (hS : s < 44/25)
    (hc : 0 ≤ c) (hC : c ≤ 13/25) :
    x^2-s*x+c=0 ↔ x=largeRoot s c ∨ x=smallRoot s c := by
  have h := nonnegative_roots s c hs hS hc hC
  have he : (x-largeRoot s c)*(x-smallRoot s c)=x^2-s*x+c := by
    linear_combination -x*h.2.2.2.2.1 + h.2.2.2.2.2
  rw [← he, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem nonnegative_roots_order (a b c : ℝ) (ha : 7/4<a) (hab : a<b) (hb : b<44/25)
    (hc : 0≤c) (hC : c≤13/25) :
    largeRoot a c < largeRoot b c ∧ smallRoot b c ≤ smallRoot a c := by
  have h := nonnegative_roots a c ha (hab.trans hb) hc hC
  have k := nonnegative_roots b c (ha.trans hab) hb hc hC
  have hd := positive_discriminant a c ha hC
  have hsq := Real.sqrt_lt_sqrt (show 0≤a^2-4*c by nlinarith [hd.1])
    (show a^2-4*c<b^2-4*c by nlinarith)
  have hp : largeRoot a c < largeRoot b c := by
    dsimp [largeRoot]
    linarith
  refine ⟨hp, ?_⟩
  by_contra hn
  have hn : smallRoot a c < smallRoot b c := lt_of_not_ge hn
  have hm := mul_lt_mul hn hp.le (show 0<largeRoot a c by linarith [h.1]) k.2.2.1
  nlinarith [h.2.2.2.2.2, k.2.2.2.2.2]

theorem largeRoot_difference (a b c : ℝ) (ha : 7/4<a) (hab : a<b) (hb : b<44/25)
    (hc : 0≤c) (hC : c≤13/25) :
    largeRoot b c - largeRoot a c < 1/50 := by
  have da := positive_discriminant a c ha hC
  have db := positive_discriminant b c (ha.trans hab) hC
  have sa := Real.sq_sqrt (show 0≤a^2-4*c by nlinarith [da.1])
  have sb := Real.sq_sqrt (show 0≤b^2-4*c by nlinarith [db.1])
  have hdiff : 0 < Real.sqrt (b^2-4*c)-Real.sqrt (a^2-4*c) := by
    have := Real.sqrt_lt_sqrt (show 0≤a^2-4*c by nlinarith [da.1])
      (show a^2-4*c < b^2-4*c by nlinarith)
    linarith
  have hm := mul_lt_mul_of_pos_left (show a+b<88/25 by linarith) (sub_pos.mpr hab)
  have hl := mul_lt_mul_of_pos_left (show 99/50<Real.sqrt (b^2-4*c)+Real.sqrt (a^2-4*c) by linarith [da.2,db.2]) hdiff
  have hroot : Real.sqrt (b^2-4*c)-Real.sqrt (a^2-4*c) < (176/99)*(b-a) := by
    nlinarith
  have hnum := scalar_numerical_bounds.2.1
  have hgap : (275/198)*(b-a) < 2*(b-a) := mul_lt_mul_of_pos_right hnum (sub_pos.mpr hab)
  dsimp [largeRoot]
  nlinarith

theorem nonnegative_product_bound {s : Fin 3 → ℝ} (hs : Admissible s)
    (c : ℝ) (hc : 0≤c) (hC : c≤13/25) :
    smallRoot (s 0) c * largeRoot (s 1) c * largeRoot (s 2) c < 1 := by
  have h0 := nonnegative_roots (s 0) c (scalar_admissible_bounds hs 0).1 (scalar_admissible_bounds hs 0).2 hc hC
  have h1 := nonnegative_roots (s 1) c (scalar_admissible_bounds hs 1).1 (scalar_admissible_bounds hs 1).2 hc hC
  have h2 := nonnegative_roots (s 2) c (scalar_admissible_bounds hs 2).1 (scalar_admissible_bounds hs 2).2 hc hC
  have hdiff := largeRoot_difference (s 0) (s 2) c hs.1 (hs.2.1.trans hs.2.2.1) hs.2.2.2 hc hC
  have hratio : largeRoot (s 2) c < (51/50)*largeRoot (s 0) c := by linarith [h0.1]
  have hmul : smallRoot (s 0) c * largeRoot (s 1) c * largeRoot (s 2) c ≤
      smallRoot (s 0) c * (44/25) * ((51/50)*largeRoot (s 0) c) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1.2.1.le h0.2.2.1) hratio.le
      (by linarith [h2.1]) (mul_nonneg h0.2.2.1 (by norm_num))
  have heq : smallRoot (s 0) c * (44/25) * ((51/50)*largeRoot (s 0) c) =
      c*(44/25)*(51/50) := by
    linear_combination (44/25)*(51/50)*h0.2.2.2.2.2
  rw [heq] at hmul
  have hstep : c*(44/25)*(51/50) ≤ (13/25)*(44/25)*(51/50) := by gcongr
  exact (hmul.trans hstep).trans_lt scalar_numerical_bounds.2.2.1

end NLA.SP04

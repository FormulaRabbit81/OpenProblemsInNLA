/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences,
California Institute of Technology.

Scalar lemmas from Sections 2--4 of the author's original IE-15 proof.
Formalized with substantial OpenAI Codex assistance.
-/
import Mathlib.Tactic

set_option autoImplicit false

namespace NLA.IE15

def scalarH (c d : ℝ) : ℝ := 3 * c * d + 1 + |c - d|

theorem scalarH_comm (c d : ℝ) : scalarH c d = scalarH d c := by
  unfold scalarH
  rw [abs_sub_comm]
  ring

theorem scalarH_nonneg {c d : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hd0 : -1 ≤ d) : 0 ≤ scalarH c d := by
  by_cases hd : 0 ≤ d
  · unfold scalarH
    positivity
  · have hdc : d ≤ c := le_trans (le_of_not_ge hd) hc0
    simp only [scalarH, abs_of_nonneg (sub_nonneg.mpr hdc)]
    have h₁ := mul_nonneg (sub_nonneg.mpr hc1) (show 0 ≤ 1-d by linarith)
    have h₂ := mul_nonneg hc0 (show 0 ≤ 1+d by linarith)
    nlinarith

theorem scalarH_le_two_add_twice_left {c d : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : -1 ≤ d) (hd1 : d ≤ 1) :
    scalarH c d ≤ 2 + 2*c := by
  by_cases hcd : c ≤ d
  · simp only [scalarH, abs_of_nonpos (sub_nonpos.mpr hcd)]
    have h := mul_nonneg (sub_nonneg.mpr hd1) (show 0 ≤ 1+3*c by positivity)
    nlinarith
  · simp only [scalarH, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hcd))]
    have h₁ := mul_nonneg (sub_nonneg.mpr hc1) (show 0 ≤ 1+d by linarith)
    have h₂ := mul_nonneg hc0 (sub_nonneg.mpr hd1)
    nlinarith

theorem scalarH_le_four {c d : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : -1 ≤ d) (hd1 : d ≤ 1) :
    scalarH c d ≤ 4 := by
  have := scalarH_le_two_add_twice_left hc0 hc1 hd0 hd1
  linarith

theorem scalarH_le_two_add_twice_right {c d : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    scalarH c d ≤ 2 + 2*d := by
  rw [scalarH_comm]
  exact scalarH_le_two_add_twice_left hd0 hd1 (by linarith) hc1

theorem scalarH_le_two_of_nonpos {c d : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : -1 ≤ d) (hd1 : d ≤ 0) :
    scalarH c d ≤ 2 := by
  simp only [scalarH, abs_of_nonneg (show 0 ≤ c-d by linarith)]
  have h₁ := mul_nonneg (sub_nonneg.mpr hc1) (show 0 ≤ 1+d by linarith)
  have h₂ := mul_nonpos_of_nonneg_of_nonpos hc0 hd1
  nlinarith

theorem scalarH_le_two_add_twice_mul {c d : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    scalarH c d ≤ 2 + 2*c*d := by
  by_cases hcd : c ≤ d
  · simp only [scalarH, abs_of_nonpos (sub_nonpos.mpr hcd)]
    have := mul_nonneg (sub_nonneg.mpr hd1) (show 0 ≤ 1+c by positivity)
    nlinarith
  · simp only [scalarH, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hcd))]
    have := mul_nonneg (sub_nonneg.mpr hc1) (show 0 ≤ 1+d by positivity)
    nlinarith

/-- Algebraic replacement for the auxiliary minimum-function monotonicity argument.
It is exact on the whole indicated box and requires no interval subdivision. -/
theorem scalar_product_bound {q x y U V : ℝ}
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hU : q*x ≤ U) (hV : q*y ≤ V) :
    2*q + 2*q*x*y ≤ 4 + U*V := by
  have hqx : 0 ≤ q*x := mul_nonneg hq0 hx0
  have hqy : 0 ≤ q*y := mul_nonneg hq0 hy0
  have hUV : (q*x)*(q*y) ≤ U*V := mul_le_mul hU hV hqy (le_trans hqx hU)
  have hxy : x*y ≤ 1 := by
    have := mul_nonneg (sub_nonneg.mpr hx1) hy0
    nlinarith
  have hqxy : q*(x*y) ≤ 2 := le_trans (mul_le_of_le_one_right hq0 hxy) hq2
  have hp := mul_nonneg (sub_nonneg.mpr hq2) (sub_nonneg.mpr hqxy)
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Section 3's full signed two-pivot inequality. -/
theorem scalar_two_pivot_bound {p q a b c₁ c₂ d₁ d₂ : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 < q)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (hc₁0 : 0 ≤ c₁) (hc₁1 : c₁ ≤ 1) (hc₂0 : 0 ≤ c₂) (hc₂1 : c₂ ≤ 1)
    (hd₁0 : -1 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hd₂0 : -1 ≤ d₂) (hd₂1 : d₂ ≤ 1)
    (h22 : |q+p*a*b| ≤ 1) (h24 : |q*d₂+p*a*d₁| ≤ 1)
    (h42 : |q*c₂+p*c₁*b| ≤ 1) :
    p*scalarH c₁ d₁ + q*scalarH c₂ d₂ ≤ 8 := by
  have h₁4 := scalarH_le_four hc₁0 hc₁1 hd₁0 hd₁1
  have h₂4 := scalarH_le_four hc₂0 hc₂1 hd₂0 hd₂1
  have hpH4 := mul_le_mul_of_nonneg_left h₁4 hp0.le
  have hqH4 := mul_le_mul_of_nonneg_left h₂4 hq0.le
  by_cases hq1 : q ≤ 1
  · nlinarith
  have hq1' : 1 < q := lt_of_not_ge hq1
  have he22 := (abs_le.mp h22).2
  have he24 := (abs_le.mp h24).2
  have he42 := (abs_le.mp h42).2
  have habs : |a*b| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (abs_le.mpr ⟨ha0,ha1⟩)
      (abs_le.mpr ⟨hb0,hb1⟩) (abs_nonneg b) (by norm_num : (0:ℝ) ≤ 1)
  have hq : q ≤ 1+p := by
    have := mul_nonneg hp0.le (show 0 ≤ a*b+1 by linarith [(abs_le.mp habs).1])
    nlinarith
  have hq2 : q ≤ 2 := by linarith
  have hab : a*b < 0 := by
    by_contra hn
    have := mul_nonneg hp0.le (le_of_not_gt hn)
    nlinarith
  have h₁c := mul_le_mul_of_nonneg_left
    (scalarH_le_two_add_twice_left hc₁0 hc₁1 hd₁0 hd₁1) hp0.le
  have h₂c := mul_le_mul_of_nonneg_left
    (scalarH_le_two_add_twice_left hc₂0 hc₂1 hd₂0 hd₂1) hq0.le
  by_cases hb : 0 < b
  · have hqb : q ≤ 1+p*b := by
      have := mul_nonneg (mul_nonneg hp0.le hb.le) (show 0 ≤ a+1 by linarith)
      nlinarith
    have hc := mul_le_of_le_one_right
      (mul_nonneg hp0.le (show 0 ≤ 1-b by linarith)) hc₁1
    nlinarith
  have hbneg : b < 0 := by
    rcases lt_or_eq_of_le (le_of_not_gt hb) with hn | hz
    · exact hn
    · subst b
      simp at hab
  have hapos : 0 < a := by
    by_contra hn
    have := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hn) hbneg.le
    linarith
  have hqa : q ≤ 1+p*a := by
    have := mul_nonneg (mul_nonneg hp0.le hapos.le) (show 0 ≤ b+1 by linarith)
    nlinarith
  by_cases hd₂ : d₂ ≤ 0
  · have h₂ := mul_le_mul_of_nonneg_left
      (scalarH_le_two_of_nonpos hc₂0 hc₂1 hd₂0 hd₂) hq0.le
    nlinarith
  have hd₂pos : 0 < d₂ := lt_of_not_ge hd₂
  by_cases hd₁ : 0 ≤ d₁
  · have h₁d := mul_le_mul_of_nonneg_left
      (scalarH_le_two_add_twice_right hc₁0 hc₁1 hd₁ hd₁1) hp0.le
    have h₂d := mul_le_mul_of_nonneg_left
      (scalarH_le_two_add_twice_right hc₂0 hc₂1 hd₂pos.le hd₂1) hq0.le
    have hd := mul_le_of_le_one_right
      (mul_nonneg hp0.le (show 0 ≤ 1-a by linarith)) hd₁1
    nlinarith
  have hd₁neg : d₁ < 0 := lt_of_not_ge hd₁
  have hpb : p*(-b) ≤ 1 := by
    have := mul_le_mul hp1 (show -b ≤ 1 by linarith)
      (show 0 ≤ -b by linarith) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith
  have hpa : p*a ≤ 1 := by
    simpa using mul_le_mul hp1 ha1 hapos.le (by norm_num : (0:ℝ) ≤ 1)
  have hU : q*c₂ ≤ 1+c₁ := by
    have := mul_nonneg (sub_nonneg.mpr hpb) hc₁0
    nlinarith
  have hV : q*d₂ ≤ 1-d₁ := by
    have := mul_nonneg (sub_nonneg.mpr hpa) (show 0 ≤ -d₁ by linarith)
    nlinarith
  have hprod := scalar_product_bound hq0.le hq2 hc₂0 hc₂1 hd₂pos.le hd₂1 hU hV
  have h₂d := mul_le_mul_of_nonneg_left
    (scalarH_le_two_add_twice_mul hc₂0 hc₂1 hd₂pos.le hd₂1) hq0.le
  have h₁nonneg := scalarH_nonneg hc₁0 hc₁1 hd₁0
  have hpH := mul_le_of_le_one_left h₁nonneg hp1
  have hcorner := mul_nonneg (sub_nonneg.mpr hc₁1) (show 0 ≤ 1+d₁ by linarith)
  have hformula : scalarH c₁ d₁ = 1+c₁-d₁+3*c₁*d₁ := by
    rw [scalarH, abs_of_nonneg (show 0 ≤ c₁-d₁ by linarith)]
    ring
  nlinarith

/-- The order-three Schur bound needed in the order-four argument.
There is no assumption on the sign of the final Schur value. -/
theorem scalar_two_pivot_cross_bound {p q a b c₁ c₂ d₁ d₂ : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 < q)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (hc₁0 : 0 ≤ c₁) (hc₁1 : c₁ ≤ 1) (hc₂0 : 0 ≤ c₂) (hc₂1 : c₂ ≤ 1)
    (hd₁0 : -1 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hd₂0 : -1 ≤ d₂) (hd₂1 : d₂ ≤ 1)
    (h22 : |q+p*a*b| ≤ 1) (h24 : |q*d₂+p*a*d₁| ≤ 1)
    (h42 : |q*c₂+p*c₁*b| ≤ 1) :
    p*c₁*d₁ + q*c₂*d₂ ≤ 2 := by
  have hh := scalar_two_pivot_bound hp0 hp1 hq0 ha0 ha1 hb0 hb1
    hc₁0 hc₁1 hc₂0 hc₂1 hd₁0 hd₁1 hd₂0 hd₂1 h22 h24 h42
  by_cases hpq : 2 ≤ p+q
  · have ha := abs_nonneg (c₁-d₁)
    have hb := abs_nonneg (c₂-d₂)
    have hpa := mul_nonneg hp0.le ha
    have hqb := mul_nonneg hq0.le hb
    unfold scalarH at hh
    nlinarith
  · have hcd₁ : c₁*d₁ ≤ 1 := by
      have := mul_nonneg hc₁0 (sub_nonneg.mpr hd₁1)
      nlinarith
    have hcd₂ : c₂*d₂ ≤ 1 := by
      have := mul_nonneg hc₂0 (sub_nonneg.mpr hd₂1)
      nlinarith
    have h₁ := mul_le_mul_of_nonneg_left hcd₁ hp0.le
    have h₂ := mul_le_mul_of_nonneg_left hcd₂ hq0.le
    nlinarith

/-- A bilinear function on the unit square is bounded by any common upper
bound of its four corners. This is the literal nonnegative-weight identity. -/
theorem scalar_bilinear_corner_bound {α β γ δ K x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h00 : δ ≤ K) (h10 : β+δ ≤ K) (h01 : γ+δ ≤ K)
    (h11 : α+β+γ+δ ≤ K) : α*x*y+β*x+γ*y+δ ≤ K := by
  have h₀₀ := mul_nonneg (sub_nonneg.mpr h00)
    (mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1))
  have h₁₀ := mul_nonneg (sub_nonneg.mpr h10)
    (mul_nonneg hx0 (sub_nonneg.mpr hy1))
  have h₀₁ := mul_nonneg (sub_nonneg.mpr h01)
    (mul_nonneg (sub_nonneg.mpr hx1) hy0)
  have h₁₁ := mul_nonneg (sub_nonneg.mpr h11) (mul_nonneg hx0 hy0)
  nlinarith only [h₀₀, h₁₀, h₀₁, h₁₁]

/-- The exact lower bound for the bilinear term in Section 4.
Both `u` and `v`, and the parameter `d`, retain their full signed domains. -/
theorem scalar_bilinear_lower {c d u v : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : -1 ≤ d) (hd1 : d ≤ 1)
    (hu0 : -1 ≤ u) (hu1 : u ≤ 1) (hv0 : -1 ≤ v) (hv1 : v ≤ 1) :
    -(u*v+d*u+c*v) ≤ 1+|c-d| := by
  have h := scalar_bilinear_corner_bound
    (α := -4) (β := 2-2*d) (γ := 2-2*c) (δ := -1+d+c)
    (K := 1+|c-d|) (x := (u+1)/2) (y := (v+1)/2)
    (by linarith : 0 ≤ (u+1)/2) (by linarith : (u+1)/2 ≤ 1)
    (by linarith : 0 ≤ (v+1)/2) (by linarith : (v+1)/2 ≤ 1)
    (by linarith [abs_nonneg (c-d)])
    (by linarith [le_abs_self (c-d)])
    (by linarith [neg_le_abs (c-d)])
    (by linarith [abs_nonneg (c-d)])
  nlinarith only [h]

end NLA.IE15

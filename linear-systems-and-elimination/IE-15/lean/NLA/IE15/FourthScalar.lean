/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences,
California Institute of Technology.

The complete order-four coordinate bound from Section 4 of the author's
original IE-15 proof, formalized with substantial OpenAI Codex assistance.
-/
import NLA.IE15.Scalar

set_option autoImplicit false

namespace NLA.IE15

theorem scalar_abs_mul_le_one {x y : ℝ}
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    |x*y| ≤ 1 := by
  rw [abs_mul]
  simpa using mul_le_mul (abs_le.mpr ⟨hx0,hx1⟩)
    (abs_le.mpr ⟨hy0,hy1⟩) (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)

theorem scalar_first_two_pivot_sum_le_three {p q a b : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (h22 : |q+p*a*b| ≤ 1) : p+q ≤ 3 := by
  have hab := (abs_le.mp (scalar_abs_mul_le_one ha0 ha1 hb0 hb1)).1
  have hmul := mul_nonneg hp0 (show 0 ≤ a*b+1 by linarith)
  have he := (abs_le.mp h22).2
  nlinarith only [hmul, he, hp1]

set_option maxHeartbeats 1000000 in
/-- All signed multiplier cases of the normalized order-four final-pivot bound.
The conclusion is the sum of the three pivot contributions, before adding the
normalized bottom-right entry (which is at most one). -/
theorem scalar_fourth_bound {p q r a b c₁ c₂ C d₁ d₂ D u₁ u₂ v₁ v₂ : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hr0 : 0 < r)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1)
    (hc₁0 : 0 ≤ c₁) (hc₁1 : c₁ ≤ 1) (hc₂0 : 0 ≤ c₂) (hc₂1 : c₂ ≤ 1)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hd₁0 : -1 ≤ d₁) (hd₁1 : d₁ ≤ 1) (hd₂0 : -1 ≤ d₂) (hd₂1 : d₂ ≤ 1)
    (_hD0 : -1 ≤ D) (hD1 : D ≤ 1)
    (hu₁0 : -1 ≤ u₁) (hu₁1 : u₁ ≤ 1) (hu₂0 : -1 ≤ u₂) (hu₂1 : u₂ ≤ 1)
    (hv₁0 : -1 ≤ v₁) (hv₁1 : v₁ ≤ 1) (hv₂0 : -1 ≤ v₂) (hv₂1 : v₂ ≤ 1)
    (h22 : |q+p*a*b| ≤ 1) (h24 : |q*d₂+p*a*d₁| ≤ 1)
    (h42 : |q*c₂+p*c₁*b| ≤ 1)
    (h33 : r+p*u₁*v₁+q*u₂*v₂ ≤ 1)
    (h34 : r*D+p*u₁*d₁+q*u₂*d₂ ≤ 1)
    (h43 : r*C+p*c₁*v₁+q*c₂*v₂ ≤ 1) :
    p*c₁*d₁+q*c₂*d₂+r*C*D ≤ 11/3 := by
  have hW := scalar_two_pivot_cross_bound hp0 hp1 hq0 ha0 ha1 hb0 hb1
    hc₁0 hc₁1 hc₂0 hc₂1 hd₁0 hd₁1 hd₂0 hd₂1 h22 h24 h42
  by_cases hD : D ≤ 0
  · have hterm := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr0.le hC0) hD
    linarith only [hW, hterm]
  have hDpos : 0 < D := lt_of_not_ge hD
  have hpq := scalar_first_two_pivot_sum_le_three hp0.le hp1 ha0 ha1 hb0 hb1 h22
  have hscalar := scalar_two_pivot_bound hp0 hp1 hq0 ha0 ha1 hb0 hb1
    hc₁0 hc₁1 hc₂0 hc₂1 hd₁0 hd₁1 hd₂0 hd₂1 h22 h24 h42
  let W := p*c₁*d₁+q*c₂*d₂
  let α := 1-p*u₁*v₁-q*u₂*v₂
  let β := 1-p*d₁*u₁-q*d₂*u₂
  let γ := 1-p*c₁*v₁-q*c₂*v₂
  have h00 : 3*W ≤ 11 := by
    dsimp [W]
    linarith only [hW]
  have h10 : β+3*W ≤ 11 := by
    have ht₁ := (abs_le.mp (scalar_abs_mul_le_one hd₁0 hd₁1 hu₁0 hu₁1)).1
    have ht₂ := (abs_le.mp (scalar_abs_mul_le_one hd₂0 hd₂1 hu₂0 hu₂1)).1
    have hp := mul_le_mul_of_nonneg_left ht₁ hp0.le
    have hq := mul_le_mul_of_nonneg_left ht₂ hq0.le
    dsimp [β, W]
    nlinarith only [hp, hq, hpq, hW]
  have h01 : γ+3*W ≤ 11 := by
    have ht₁ := (abs_le.mp (scalar_abs_mul_le_one (by linarith : -1 ≤ c₁)
      hc₁1 hv₁0 hv₁1)).1
    have ht₂ := (abs_le.mp (scalar_abs_mul_le_one (by linarith : -1 ≤ c₂)
      hc₂1 hv₂0 hv₂1)).1
    have hp := mul_le_mul_of_nonneg_left ht₁ hp0.le
    have hq := mul_le_mul_of_nonneg_left ht₂ hq0.le
    dsimp [γ, W]
    nlinarith only [hp, hq, hpq, hW]
  have h11 : α+β+γ+3*W ≤ 11 := by
    have ht₁ := scalar_bilinear_lower hc₁0 hc₁1 hd₁0 hd₁1 hu₁0 hu₁1 hv₁0 hv₁1
    have ht₂ := scalar_bilinear_lower hc₂0 hc₂1 hd₂0 hd₂1 hu₂0 hu₂1 hv₂0 hv₂1
    have hp := mul_le_mul_of_nonneg_left ht₁ hp0.le
    have hq := mul_le_mul_of_nonneg_left ht₂ hq0.le
    dsimp [α, β, γ, W]
    unfold scalarH at hscalar
    nlinarith only [hp, hq, hscalar]
  have hB := scalar_bilinear_corner_bound hC0 hC1 hDpos.le hD1 h00 h10 h01 h11
  have h33' := mul_le_mul_of_nonneg_left h33 (mul_nonneg hC0 hDpos.le)
  have h34' := mul_le_mul_of_nonneg_left h34 hC0
  have h43' := mul_le_mul_of_nonneg_left h43 hDpos.le
  dsimp [α, β, γ, W] at hB
  nlinarith only [hB, h33', h34', h43']

end NLA.IE15

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences,
California Institute of Technology.

The original mathematical resolution is George Stepaniants's 11 September
2026 proof. This formalization uses substantial OpenAI Codex assistance.
-/
import NLA.IE15.Coordinates
import NLA.IE15.FourthScalar

set_option autoImplicit false
noncomputable section
namespace NLA.IE15

/-- The first two genuine elimination coordinates satisfy the scalar
cross bound. The selected later row need not be the last row. -/
theorem normalized_two_pivot_cross_bound {n : ℕ} (A : Mat (n+3))
    (hp : AdmissiblePath A (noSwapPath (n+3)))
    (hA : ∀ i j, |A i j| ≤ 1)
    (hpos : ∀ k, 0 < diagPivot A k)
    (t : Fin (n+3)) (ht : 1 < t.val)
    (hl₀ : 0 ≤ lowerMultiplier A t 0)
    (hl₁ : 0 ≤ lowerMultiplier A t 1) :
    diagPivot A 0 * lowerMultiplier A t 0 * (-upperMultiplier A 0 t) +
      diagPivot A 1 * lowerMultiplier A t 1 * (-upperMultiplier A 1 t) ≤ 2 := by
  have hp1 : diagPivot A 0 ≤ 1 := by
    have h := hA 0 0
    have hz : diagPivot A 0 = A 0 0 := by simp [diagPivot, trajectory]
    rw [← hz, abs_of_pos (hpos 0)] at h
    exact h
  have hab := abs_le.mp (lowerMultiplier_bound A hp 1 0 (by simp))
  have hbb := abs_le.mp (upperMultiplier_bound A hp 0 1 (by simp))
  have hc₀ := abs_le.mp (lowerMultiplier_bound A hp t 0 (by simp))
  have hc₁ := abs_le.mp (lowerMultiplier_bound A hp t 1 (by simpa only [Fin.le_def, Fin.val_one] using ht.le))
  have hd₀ := abs_le.mp (upperMultiplier_bound A hp 0 t (by simp))
  have hd₁ := abs_le.mp (upperMultiplier_bound A hp 1 t (by simpa only [Fin.le_def, Fin.val_one] using ht.le))
  have e11 := entry_prefix_coordinates A hp 1 (1 : Fin (n+3)) 1 (by simp) (by simp)
  have e1t := entry_prefix_coordinates A hp 1 (1 : Fin (n+3)) t (by simp) ht.le
  have et1 := entry_prefix_coordinates A hp 1 t (1 : Fin (n+3)) ht.le (by simp)
  have hz : 0 < n+3 := by omega
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, updateTerm,
    dif_pos hz] at e11 e1t et1
  have hzero : (⟨0, hz⟩ : Fin (n+3)) = 0 := by ext; simp
  rw [hzero] at e11 e1t et1
  have ed : trajectory A (noSwapPath (n+3)) 1 1 1 = diagPivot A 1 := by
    simp [diagPivot]
  have er := pivot_mul_upperMultiplier A hp 1 t
  have ec := lowerMultiplier_mul_pivot A hp t 1
  simp only [Fin.val_one] at er ec
  rw [ed] at e11
  rw [← er] at e1t
  rw [← ec] at et1
  have h11 : |diagPivot A 1 + diagPivot A 0 * lowerMultiplier A 1 0 *
      upperMultiplier A 0 1| ≤ 1 := by
    convert hA 1 1 using 1
    congr 1
    rw [e11]
    ring
  have h1t : |diagPivot A 1 * (-upperMultiplier A 1 t) +
      diagPivot A 0 * lowerMultiplier A 1 0 * (-upperMultiplier A 0 t)| ≤ 1 := by
    rw [show diagPivot A 1 * (-upperMultiplier A 1 t) +
      diagPivot A 0 * lowerMultiplier A 1 0 * (-upperMultiplier A 0 t) = -A 1 t by
        rw [e1t]; ring, abs_neg]
    exact hA 1 t
  have ht1 : |diagPivot A 1 * lowerMultiplier A t 1 +
      diagPivot A 0 * lowerMultiplier A t 0 * upperMultiplier A 0 1| ≤ 1 := by
    convert hA t 1 using 1
    congr 1
    rw [et1]
    ring
  exact scalar_two_pivot_cross_bound (hpos 0) hp1 (hpos 1)
    hab.1 hab.2 hbb.1 hbb.2 hl₀ hc₀.2 hl₁ hc₁.2
    (by linarith [hd₀.2]) (by linarith [hd₀.1])
    (by linarith [hd₁.2]) (by linarith [hd₁.1]) h11 h1t ht1

/-- The order-three bound under the manuscript's positive-pivot and
nonnegative last-row normalization, using the original input entries. -/
theorem normalized_final_pivot_three (A : Mat 3)
    (hp : AdmissiblePath A (noSwapPath 3))
    (hA : ∀ i j, |A i j| ≤ 1)
    (hpos : ∀ k, 0 < diagPivot A k)
    (hL : ∀ k : Fin 3, k < 2 → 0 ≤ lowerMultiplier A 2 k) :
    diagPivot A 2 ≤ 3 := by
  have hcross := normalized_two_pivot_cross_bound (n := 0) A hp hA hpos 2
    (by decide) (hL 0 (by decide)) (hL 1 (by decide))
  have e := entry_prefix_coordinates A hp 2 (2 : Fin 3) 2 (by decide) (by decide)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    updateTerm, show 0 < 3 by decide, show 1 < 3 by decide, dif_pos] at e
  change A 2 2 = diagPivot A 2 +
    (lowerMultiplier A 2 0 * diagPivot A 0 * upperMultiplier A 0 2 +
      lowerMultiplier A 2 1 * diagPivot A 1 * upperMultiplier A 1 2) at e
  have hlast := (abs_le.mp (hA 2 2)).2
  nlinarith only [e, hlast, hcross]

/-- The complete order-four bound under the manuscript's normalization.
No modification of the original bottom-right entry is needed: its existing
upper bound by one suffices in the reconstruction identity. -/
theorem normalized_final_pivot_four (A : Mat 4)
    (hp : AdmissiblePath A (noSwapPath 4))
    (hA : ∀ i j, |A i j| ≤ 1)
    (hpos : ∀ k, 0 < diagPivot A k)
    (hL : ∀ k : Fin 4, k < 3 → 0 ≤ lowerMultiplier A 3 k) :
    diagPivot A 3 ≤ (14/3 : ℝ) := by
  let p := diagPivot A 0
  let q := diagPivot A 1
  let r := diagPivot A 2
  let a := lowerMultiplier A 1 0
  let b := upperMultiplier A 0 1
  let c₁ := lowerMultiplier A 3 0
  let c₂ := lowerMultiplier A 3 1
  let C := lowerMultiplier A 3 2
  let d₁ := -upperMultiplier A 0 3
  let d₂ := -upperMultiplier A 1 3
  let D := -upperMultiplier A 2 3
  let u₁ := lowerMultiplier A 2 0
  let u₂ := lowerMultiplier A 2 1
  let v₁ := upperMultiplier A 0 2
  let v₂ := upperMultiplier A 1 2
  have hp1 : p ≤ 1 := by
    have h := hA 0 0
    change |p| ≤ 1 at h
    rwa [abs_of_pos (hpos 0)] at h
  have pref1 (i j : Fin 4) (hi : 1 ≤ i.val) (hj : 1 ≤ j.val) :
      A i j = trajectory A (noSwapPath 4) 1 i j +
        lowerMultiplier A i 0 * p * upperMultiplier A 0 j := by
    have h := entry_prefix_coordinates A hp 1 i j hi hj
    norm_num [Finset.sum_range_succ, updateTerm] at h
    exact h
  have pref2 (i j : Fin 4) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val) :
      A i j = trajectory A (noSwapPath 4) 2 i j +
        (lowerMultiplier A i 0 * p * upperMultiplier A 0 j +
        lowerMultiplier A i 1 * q * upperMultiplier A 1 j) := by
    have h := entry_prefix_coordinates A hp 2 i j hi hj
    norm_num [Finset.sum_range_succ, updateTerm] at h
    exact h
  have e11 : A 1 1 = q+p*a*b := by
    rw [pref1 1 1 (by decide) (by decide)]
    change q + a*p*b = q+p*a*b
    ring
  have e13 : A 1 3 = -(q*d₂+p*a*d₁) := by
    rw [pref1 1 3 (by decide) (by decide)]
    have he := pivot_mul_upperMultiplier A hp 1 3
    rw [show trajectory A (noSwapPath 4) 1 1 3 =
      diagPivot A 1 * upperMultiplier A 1 3 from he.symm]
    dsimp [q, a, b, d₁, d₂]
    ring
  have e31 : A 3 1 = q*c₂+p*c₁*b := by
    rw [pref1 3 1 (by decide) (by decide)]
    have he := lowerMultiplier_mul_pivot A hp 3 1
    rw [show trajectory A (noSwapPath 4) 1 3 1 =
      lowerMultiplier A 3 1 * diagPivot A 1 from he.symm]
    dsimp [q, c₁, c₂, b]
    ring
  have e22 : A 2 2 = r+p*u₁*v₁+q*u₂*v₂ := by
    rw [pref2 2 2 (by decide) (by decide)]
    change r + (u₁*p*v₁+u₂*q*v₂) = r+p*u₁*v₁+q*u₂*v₂
    ring
  have e23 : A 2 3 = -(r*D+p*u₁*d₁+q*u₂*d₂) := by
    rw [pref2 2 3 (by decide) (by decide)]
    have he := pivot_mul_upperMultiplier A hp 2 3
    rw [show trajectory A (noSwapPath 4) 2 2 3 =
      diagPivot A 2 * upperMultiplier A 2 3 from he.symm]
    dsimp [r, u₁, u₂, d₁, d₂, D]
    ring
  have e32 : A 3 2 = r*C+p*c₁*v₁+q*c₂*v₂ := by
    rw [pref2 3 2 (by decide) (by decide)]
    have he := lowerMultiplier_mul_pivot A hp 3 2
    rw [show trajectory A (noSwapPath 4) 2 3 2 =
      lowerMultiplier A 3 2 * diagPivot A 2 from he.symm]
    dsimp [r, C, c₁, c₂, v₁, v₂]
    ring
  have h11 : |q+p*a*b| ≤ 1 := by rw [← e11]; exact hA 1 1
  have h13 : |q*d₂+p*a*d₁| ≤ 1 := by
    have h := hA 1 3
    rwa [e13, abs_neg] at h
  have h31 : |q*c₂+p*c₁*b| ≤ 1 := by rw [← e31]; exact hA 3 1
  have h22 : r+p*u₁*v₁+q*u₂*v₂ ≤ 1 := by
    rw [← e22]
    exact (abs_le.mp (hA 2 2)).2
  have h23 : r*D+p*u₁*d₁+q*u₂*d₂ ≤ 1 := by
    have h := (abs_le.mp (hA 2 3)).1
    rw [e23] at h
    linarith only [h]
  have h32 : r*C+p*c₁*v₁+q*c₂*v₂ ≤ 1 := by
    rw [← e32]
    exact (abs_le.mp (hA 3 2)).2
  have hbL (i k : Fin 4) (hik : k ≤ i) := abs_le.mp (lowerMultiplier_bound A hp i k hik)
  have hbR (k j : Fin 4) (hkj : k ≤ j) := abs_le.mp (upperMultiplier_bound A hp k j hkj)
  have hd₁ := hbR 0 3 (by decide)
  have hd₂ := hbR 1 3 (by decide)
  have hD := hbR 2 3 (by decide)
  have htotal := scalar_fourth_bound (p := p) (q := q) (r := r)
    (a := a) (b := b) (c₁ := c₁) (c₂ := c₂) (C := C)
    (d₁ := d₁) (d₂ := d₂) (D := D) (u₁ := u₁) (u₂ := u₂) (v₁ := v₁) (v₂ := v₂)
    (hpos 0) hp1 (hpos 1) (hpos 2)
    (hbL 1 0 (by decide)).1 (hbL 1 0 (by decide)).2
    (hbR 0 1 (by decide)).1 (hbR 0 1 (by decide)).2
    (hL 0 (by decide)) (hbL 3 0 (by decide)).2
    (hL 1 (by decide)) (hbL 3 1 (by decide)).2
    (hL 2 (by decide)) (hbL 3 2 (by decide)).2
    (by dsimp [d₁]; linarith [hd₁.2]) (by dsimp [d₁]; linarith [hd₁.1])
    (by dsimp [d₂]; linarith [hd₂.2]) (by dsimp [d₂]; linarith [hd₂.1])
    (by dsimp [D]; linarith [hD.2]) (by dsimp [D]; linarith [hD.1])
    (hbL 2 0 (by decide)).1 (hbL 2 0 (by decide)).2
    (hbL 2 1 (by decide)).1 (hbL 2 1 (by decide)).2
    (hbR 0 2 (by decide)).1 (hbR 0 2 (by decide)).2
    (hbR 1 2 (by decide)).1 (hbR 1 2 (by decide)).2
    h11 h13 h31 h22 h23 h32
  have e := entry_prefix_coordinates A hp 3 (3 : Fin 4) 3 (by decide) (by decide)
  norm_num [Finset.sum_range_succ, updateTerm] at e
  change A 3 3 = diagPivot A 3 +
    (lowerMultiplier A 3 0 * diagPivot A 0 * upperMultiplier A 0 3 +
      lowerMultiplier A 3 1 * diagPivot A 1 * upperMultiplier A 1 3 +
      lowerMultiplier A 3 2 * diagPivot A 2 * upperMultiplier A 2 3) at e
  dsimp only [p, q, r, c₁, c₂, C, d₁, d₂, D] at htotal
  have hlast := (abs_le.mp (hA 3 3)).2
  nlinarith only [e, hlast, htotal]

end NLA.IE15

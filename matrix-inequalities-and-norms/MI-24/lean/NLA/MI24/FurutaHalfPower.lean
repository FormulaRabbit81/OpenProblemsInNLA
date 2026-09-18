/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Only one finite extension of Fujii's base range is needed: use A1=A^2 and
B1=(A^(1/2) B^2 A^(1/2))^(2/3), then apply the base theorem at s=3/2.
A final Loewner-Heinz power gives the complete frozen q=2 Furuta contract.
-/
import NLA.MI24.FurutaBase

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

lemma spectralPower_two {n : ℕ} (A : Mat n) (hA : A.PosDef) :
    spectralPower A 2 = A * A := by
  calc
    spectralPower A 2 = spectralPower A 1 * spectralPower A 1 := by
      rw [spectralPower_mul A hA]
      norm_num
    _ = A * A := by rw [spectralPower_one A hA]

lemma furuta_grade_two {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (hBA : B ≤ A) (R : ℝ) (hR0 : 0 ≤ R) (hR2 : R ≤ 2) :
    spectralPower
      (spectralPower A (R / 2) * spectralPower B 2 * spectralPower A (R / 2))
      ((1 + R) / (2 + R)) ≤ spectralPower A (1 + R) := by
  by_cases hR1 : R ≤ 1
  · exact furuta_base A B hA hB hBA 2 R (by norm_num) hR0 hR1
  · have hRlower : 1 ≤ R := le_of_lt (lt_of_not_ge hR1)
    let A₁ := spectralPower A 2
    let D₀ := spectralPower A (1 / 2) * spectralPower B 2 * spectralPower A (1 / 2)
    let B₁ := spectralPower D₀ (2 / 3)
    let t := (R - 1) / 2
    have ht0 : 0 ≤ t := by dsimp only [t]; linarith
    have ht1 : t ≤ 1 := by dsimp only [t]; linarith
    have hA₁ : A₁.PosDef := spectralPower_posDef A hA _
    have hD₀ : D₀.PosDef := posDef_hermitian_sandwich _ _
      (spectralPower_posDef B hB _) (spectralPower_isHermitian A hA _)
      (spectralPower_isUnit A hA _)
    have hB₁ : B₁.PosDef := spectralPower_posDef D₀ hD₀ _
    have hB₁A₁ : B₁ ≤ A₁ := by
      have h := furuta_base A B hA hB hBA 2 1 (by norm_num) (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hBpow : spectralPower B₁ (3 / 2) = D₀ := by
      -- Expose the local B₁ power of D₀ so spectralPower_comp applies to
      -- the nested functional calculus rather than to the abbreviation.
      change spectralPower (spectralPower D₀ (2 / 3)) (3 / 2) = D₀
      rw [spectralPower_comp D₀ hD₀,
        -- Identify the exact real exponent product with 1 before applying
        -- the first-power identity; the equality is discharged by norm_num.
        show ((2 / 3 : ℝ) * (3 / 2)) = 1 by norm_num,
        spectralPower_one D₀ hD₀]
    have hApow : spectralPower A₁ (t / 2) = spectralPower A t := by
      dsimp only [A₁]
      rw [spectralPower_comp A hA]
      congr 1
      ring
    have hleft : t + 1 / 2 = R / 2 := by dsimp only [t]; ring
    have hright : 1 / 2 + t = R / 2 := by dsimp only [t]; ring
    have hinner :
        spectralPower A₁ (t / 2) * spectralPower B₁ (3 / 2) * spectralPower A₁ (t / 2) =
          spectralPower A (R / 2) * spectralPower B 2 * spectralPower A (R / 2) := by
      rw [hApow, hBpow]
      calc
        spectralPower A t * D₀ * spectralPower A t =
            (spectralPower A t * spectralPower A (1 / 2)) * spectralPower B 2 *
              (spectralPower A (1 / 2) * spectralPower A t) := by
          dsimp only [D₀]
          simp only [mul_assoc]
        _ = spectralPower A (R / 2) * spectralPower B 2 * spectralPower A (R / 2) := by
          rw [spectralPower_mul A hA, spectralPower_mul A hA, hleft, hright]
    have hout : spectralPower A₁ (1 + t) = spectralPower A (1 + R) := by
      dsimp only [A₁]
      rw [spectralPower_comp A hA]
      congr 1
      dsimp only [t]
      ring
    have hexp : (1 + t) / (3 / 2 + t) = (1 + R) / (2 + R) := by
      apply (div_eq_div_iff (by dsimp only [t]; linarith) (by linarith)).mpr
      dsimp only [t]
      ring
    have h := furuta_base A₁ B₁ hA₁ hB₁ hB₁A₁ (3 / 2) t (by norm_num) ht0 ht1
    rwa [hinner, hout, hexp] at h

theorem furuta_half_power {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (hYX : Y ≤ X)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    spectralPower (spectralPower X r * (Y * Y) * spectralPower X r) (1 / 2) ≤
      spectralPower X (1 + r) := by
  let R := 2 * r
  let a := (1 + R) / (2 + R)
  let b := (2 + R) / (2 * (1 + R))
  let D := spectralPower X (R / 2) * spectralPower Y 2 * spectralPower X (R / 2)
  have hR0 : 0 ≤ R := by dsimp only [R]; linarith
  have hR2 : R ≤ 2 := by dsimp only [R]; linarith
  have hden : 0 < 2 * (1 + R) := by linarith
  have hden₁ : 1 + R ≠ 0 := by linarith
  have hden₂ : 2 + R ≠ 0 := by linarith
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact div_nonneg (by linarith) hden.le
  have hb1 : b ≤ 1 := by
    dsimp only [b]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hD : D.PosDef := posDef_hermitian_sandwich _ _
    (spectralPower_posDef Y hY _) (spectralPower_isHermitian X hX _)
    (spectralPower_isUnit X hX _)
  have hbase : spectralPower D a ≤ spectralPower X (1 + R) :=
    furuta_grade_two X Y hX hY hYX R hR0 hR2
  have h := spectralPower_order _ _ hbase b hb0 hb1
  rw [spectralPower_comp D hD, spectralPower_comp X hX] at h
  have hab : a * b = 1 / 2 := by
    dsimp only [a, b]
    field_simp [hden₁, hden₂]
  have hout : (1 + R) * b = 1 + r := by
    dsimp only [b]
    field_simp [hden₁]
    dsimp only [R]
    ring
  rw [hab, hout] at h
  have hinner : D = spectralPower X r * (Y * Y) * spectralPower X r := by
    dsimp only [D, R]
    -- Normalize the real half-exponent back to r, aligning the inner
    -- sandwich with the named D before rewriting the square of Y.
    rw [show (2 * r / 2 : ℝ) = r by ring, spectralPower_two Y hY]
  rwa [hinner] at h

end NLA.MI24

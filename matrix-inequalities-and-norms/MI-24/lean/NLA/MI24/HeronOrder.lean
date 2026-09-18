/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The order implication in Dinh--Dumitru--Franco's weighted trace comparison.
This is only its operator-order foundation: the passage through every compound
degree and weak log-majorization is still required for the full trace theorem.
-/
import NLA.MI24.FurutaHalfPower

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI24

/-- The positive matrix whose trace is the left side of the weighted comparison. -/
def weightedHeronSource {n : ℕ} (P D : Mat n) (p : ℝ) : Mat n :=
  spectralPower P (p / 2) *
    spectralPower (spectralPower P (-1 / 2) * D * spectralPower P (-1 / 2)) (1 / 2) *
      spectralPower P (p / 2)

/-- The positive matrix whose trace is the right side of the weighted comparison. -/
def weightedHeronTarget {n : ℕ} (P D : Mat n) (p : ℝ) : Mat n :=
  spectralPower P ((p - 1 / 2) / 2) * spectralPower D (1 / 2) *
    spectralPower P ((p - 1 / 2) / 2)

lemma weightedHeronSource_posDef {n : ℕ} (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) :
    (weightedHeronSource P D p).PosDef :=
  posDef_hermitian_sandwich _ _
    (spectralPower_posDef _ (geometric_inner_posDef P D hP hD) _)
    (spectralPower_isHermitian P hP _) (spectralPower_isUnit P hP _)

lemma weightedHeronTarget_posDef {n : ℕ} (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) :
    (weightedHeronTarget P D p).PosDef :=
  posDef_hermitian_sandwich _ _ (spectralPower_posDef D hD _)
    (spectralPower_isHermitian P hP _) (spectralPower_isUnit P hP _)

/-- Invertible congruence removes both outer powers without commuting them
through the arbitrary middle matrix. -/
lemma spectralPower_sandwich_le_one {n : ℕ} (P Y : Mat n)
    (hP : P.PosDef) (a : ℝ)
    (h : spectralPower P a * Y * spectralPower P a ≤ 1) :
    Y ≤ spectralPower P (-2 * a) := by
  have hc := hermitian_sandwich_order _ _ (spectralPower P (-a)) h
    (spectralPower_isHermitian P hP _)
  have hleft : spectralPower P (-a) *
      (spectralPower P a * Y * spectralPower P a) * spectralPower P (-a) = Y := by
    calc
      _ = (spectralPower P (-a) * spectralPower P a) * Y *
          (spectralPower P a * spectralPower P (-a)) := by simp only [mul_assoc]
      _ = Y := by
        rw [spectralPower_neg_mul P hP, spectralPower_mul_neg P hP]
        simp only [one_mul, mul_one]
  have hright : spectralPower P (-a) * 1 * spectralPower P (-a) =
      spectralPower P (-2 * a) := by
    rw [mul_one, spectralPower_mul P hP]
    congr 1
    ring
  rwa [hleft, hright] at hc

lemma weightedHeronSource_le_one {n : ℕ} (hn : 1 ≤ n) (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p : ℝ) (hp : 1 ≤ p)
    (hT : weightedHeronTarget P D p ≤ 1) : weightedHeronSource P D p ≤ 1 := by
  let X := spectralPower P (1 / 2 - p)
  let Y := spectralPower D (1 / 2)
  let r := 1 / (2 * p - 1)
  have hden : 0 < 2 * p - 1 := by linarith
  have hdenne : 2 * p - 1 ≠ 0 := ne_of_gt hden
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp only [r]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hYX : Y ≤ X := by
    have h := spectralPower_sandwich_le_one P Y hP ((p - 1 / 2) / 2) hT
    -- Normalize the real exponent produced by undoing the sandwich to
    -- the chosen X exponent 1/2 - p; ring proves the syntactic conversion.
    rwa [show (-2 * ((p - 1 / 2) / 2) : ℝ) = 1 / 2 - p by ring] at h
  have hX : X.PosDef := spectralPower_posDef P hP _
  have hY : Y.PosDef := spectralPower_posDef D hD _
  have hxpow : spectralPower X r = spectralPower P (-1 / 2) := by
    dsimp only [X]
    rw [spectralPower_comp P hP]
    congr 1
    dsimp only [r]
    field_simp [hdenne]
    ring
  have hout : spectralPower X (1 + r) = spectralPower P (-p) := by
    dsimp only [X]
    rw [spectralPower_comp P hP]
    congr 1
    dsimp only [r]
    field_simp [hdenne]
    ring
  have hyprod : Y * Y = D := spectralPower_half_mul_self D hD
  have hfuruta := furuta_half_power hn X Y hX hY hYX r hr0 hr1
  rw [hxpow, hout, hyprod] at hfuruta
  have h := hermitian_sandwich_order _ _ (spectralPower P (p / 2)) hfuruta
    (spectralPower_isHermitian P hP _)
  have hunit : spectralPower P (p / 2) * spectralPower P (-p) *
      spectralPower P (p / 2) = 1 := by
    rw [spectralPower_sandwich_same P hP,
      -- Combine the three real exponents to zero so spectralPower_zero
      -- reduces the enclosing sandwich to the identity matrix.
      show (2 * (p / 2) + -p : ℝ) = 0 by ring, spectralPower_zero P hP]
  rwa [hunit] at h

/-- Positive scalar square-root scaling is proved by uniqueness of the actual
positive square root, so no scalar CFC identity is assumed. -/
lemma spectralPower_smul_sq_half {n : ℕ} (A : Mat n) (hA : A.PosDef)
    (c : ℝ) (hc : 0 < c) :
    spectralPower ((c : ℂ) ^ 2 • A) (1 / 2) =
      (c : ℂ) • spectralPower A (1 / 2) := by
  apply spectralPower_half_unique
  · exact (spectralPower_posDef A hA _).smul (by
      exact_mod_cast hc)
  · simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      spectralPower_half_mul_self A hA, pow_two]

lemma weightedHeronSource_smul_sq {n : ℕ} (P D : Mat n)
    (hP : P.PosDef) (hD : D.PosDef) (p c : ℝ) (hc : 0 < c) :
    weightedHeronSource P ((c : ℂ) ^ 2 • D) p =
      (c : ℂ) • weightedHeronSource P D p := by
  unfold weightedHeronSource
  rw [mul_smul_comm, smul_mul_assoc,
    spectralPower_smul_sq_half _ (geometric_inner_posDef P D hP hD) c hc]
  simp only [mul_smul_comm, smul_mul_assoc]

lemma weightedHeronTarget_smul_sq {n : ℕ} (P D : Mat n)
    (hD : D.PosDef) (p c : ℝ) (hc : 0 < c) :
    weightedHeronTarget P ((c : ℂ) ^ 2 • D) p =
      (c : ℂ) • weightedHeronTarget P D p := by
  unfold weightedHeronTarget
  rw [spectralPower_smul_sq_half D hD c hc]
  simp only [mul_smul_comm, smul_mul_assoc]

end NLA.MI24

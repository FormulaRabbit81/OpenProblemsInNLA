/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of Technology.
This file transports the analytic final-pivot bound back to every entry of
every admissible rook trajectory. Implemented with OpenAI Codex assistance.
-/
import NLA.IE15.Permutation
import NLA.IE15.Normalization

noncomputable section
namespace NLA.IE15

/-- A reusable reduction with an explicit remaining analytic obligation. The final
exports discharge that obligation separately in both dimensions. -/
theorem all_entries_bound_from_normalized {n : ℕ} (hn : 1 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (hstage : ∀ k : Fin n, k.val < n - 1 → (2 : ℝ)^k.val ≤ C)
    (hfinal : ∀ (B : Mat n) (last : Fin n), last.val = n - 1 →
      AdmissiblePath B (noSwapPath n) →
      (∀ i j, |B i j| ≤ 1) →
      (∀ i : Fin n, 0 < trajectory B (noSwapPath n) i.val i i) →
      (∀ i : Fin n, i < last → 0 ≤
        trajectory B (noSwapPath n) i.val last i /
          trajectory B (noSwapPath n) i.val i i) →
      trajectory B (noSwapPath n) last.val last last ≤ C)
    (A : Mat n) (path : PivotPath n) (hp : AdmissiblePath A path) :
    ∀ k i j : Fin n, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ C * entryMax A := by
  obtain ⟨B, hBA, hpB, hstages⟩ := exists_noSwap_representative A path hp
  let last : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨D, hpD, hDentries, hDpos, hDlower, hDscale⟩ :=
    exists_normalized_noSwap hn B hpB last
  have hM : 0 < entryMax B := entryMax_pos_of_admissible_proved hn B (noSwapPath n) hpB
  have hDlast := hfinal D last rfl hpD hDentries hDpos hDlower
  have hBlast : |trajectory B (noSwapPath n) last.val last last| ≤ C * entryMax B := by
    apply (div_le_iff₀ hM).mp
    rw [← hDscale last.val last last, abs_of_pos (hDpos last)]
    exact hDlast
  have hBmax : activeMax (trajectory B (noSwapPath n) last.val) last.val ≤
      C * entryMax B := by
    apply activeMax_le_proved _ _ _ (mul_nonneg hC hM.le)
    intro i j hi hj
    have hi' : i = last := by apply Fin.ext; dsimp [last] at hi ⊢; omega
    have hj' : j = last := by apply Fin.ext; dsimp [last] at hj ⊢; omega
    simpa [hi', hj'] using hBlast
  intro k i j hi hj
  apply (abs_le_activeMax_proved (trajectory A path k.val) k.val i j hi hj).trans
  by_cases hk : k.val < n - 1
  · exact (rook_stage_bound_proved A path hp k.val k.isLt).trans
      (mul_le_mul_of_nonneg_right (hstage k hk) (entryMax_nonneg_proved A))
  · have hk' : k = last := by apply Fin.ext; dsimp [last]; omega
    subst k
    rw [← hstages last, ← hBA]
    exact hBmax

end NLA.IE15

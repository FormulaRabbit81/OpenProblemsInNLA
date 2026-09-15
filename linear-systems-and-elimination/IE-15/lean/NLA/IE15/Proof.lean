/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of Technology.
Full formalization of George Stepaniants's original IE-15 resolution.
Substantial OpenAI Codex assistance; no claim of external human peer review.
-/
import NLA.IE15.Reduction
import NLA.IE15.NormalizedBounds
import NLA.IE15.Witnesses
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.IE15

/-- Exact certificate used to include the third active stage in the order-four bound. -/
theorem four_le_fourteen_thirds : (4 : ℝ) ≤ 14 / 3 := by
  leancert (trust := kernel)

theorem entryMax_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, |A i j| ≤ entryMax A) ∧
      ∃ i j, entryMax A = |A i j| :=
  entryMax_semantics_proved hn A

theorem all_entries_bound_three (A : Mat 3) (_hA : A.det ≠ 0)
    (path : PivotPath 3) (hp : AdmissiblePath A path) :
    ∀ k i j : Fin 3, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ 3 * entryMax A := by
  apply all_entries_bound_from_normalized (by decide) 3 (by norm_num) ?_ ?_ A path hp
  · intro k hk
    fin_cases k <;> norm_num at *
  · intro B last hlast hpB hB hpos hL
    have he : last = (2 : Fin 3) := by apply Fin.ext; exact hlast
    subst last
    exact normalized_final_pivot_three B hpB hB hpos hL

theorem all_entries_bound_four (A : Mat 4) (_hA : A.det ≠ 0)
    (path : PivotPath 4) (hp : AdmissiblePath A path) :
    ∀ k i j : Fin 4, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ (14/3 : ℝ) * entryMax A := by
  apply all_entries_bound_from_normalized (by decide) (14/3) (by norm_num) ?_ ?_ A path hp
  · intro k hk
    have hfour : (2 : ℝ)^k.val ≤ 4 := by fin_cases k <;> norm_num at *
    exact hfour.trans four_le_fourteen_thirds
  · intro B last hlast hpB hB hpos hL
    have he : last = (3 : Fin 4) := by apply Fin.ext; exact hlast
    subst last
    exact normalized_final_pivot_four B hpB hB hpos hL

theorem witness_three :
    witness3.det = 3 ∧ entryMax witness3 = 1 ∧
      AdmissiblePath witness3 (noSwapPath 3) ∧
      growth witness3 (noSwapPath 3) = 3 := witness_three_proved

theorem witness_four :
    witness4.det = (70/9 : ℝ) ∧ entryMax witness4 = 1 ∧
      AdmissiblePath witness4 (noSwapPath 4) ∧
      growth witness4 (noSwapPath 4) = (14/3 : ℝ) := witness_four_proved

theorem greatest_growth_three : IsGreatest (growthSet 3) 3 := by
  constructor
  · refine ⟨witness3, ?_, noSwapPath 3, witness_three.2.2.1, witness_three.2.2.2.symm⟩
    rw [witness_three.1]
    norm_num
  · rintro x ⟨A, hA, path, hp, rfl⟩
    exact growth_le_of_entries_proved (by decide) A path hp 3 (by norm_num)
      (all_entries_bound_three A hA path hp)

theorem greatest_growth_four : IsGreatest (growthSet 4) (14/3 : ℝ) := by
  constructor
  · refine ⟨witness4, ?_, noSwapPath 4, witness_four.2.2.1, witness_four.2.2.2.symm⟩
    rw [witness_four.1]
    norm_num
  · rintro x ⟨A, hA, path, hp, rfl⟩
    exact growth_le_of_entries_proved (by decide) A path hp (14/3) (by norm_num)
      (all_entries_bound_four A hA path hp)

theorem exact_rook_growth :
    rookGrowthSup 3 = 3 ∧ rookGrowthSup 4 = (14/3 : ℝ) := by
  exact ⟨greatest_growth_three.isLUB.csSup_eq ⟨3, greatest_growth_three.1⟩,
    greatest_growth_four.isLUB.csSup_eq ⟨14/3, greatest_growth_four.1⟩⟩

#assert_trust kernel four_le_fourteen_thirds
#assert_trust kernel entryMax_semantics
#assert_trust kernel all_entries_bound_three
#assert_trust kernel all_entries_bound_four
#assert_trust kernel witness_three
#assert_trust kernel witness_four
#assert_trust kernel greatest_growth_three
#assert_trust kernel greatest_growth_four
#assert_trust kernel exact_rook_growth

#print axioms four_le_fourteen_thirds
#print axioms entryMax_semantics
#print axioms all_entries_bound_three
#print axioms all_entries_bound_four
#print axioms witness_three
#print axioms witness_four
#print axioms greatest_growth_three
#print axioms greatest_growth_four
#print axioms exact_rook_growth

end NLA.IE15

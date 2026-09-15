import NLA.IE15.Definitions

/-!
# IE-15: independently reviewed statement environment

These deliberate placeholders are only a proposed specification. They prove
no mathematics, and the solution environment must never import this module.
Proof implementation starts only after type-checking and two independent
statement approvals of the exact boundary bytes.
-/

set_option autoImplicit false
noncomputable section
namespace NLA.IE15

theorem entryMax_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, |A i j| ≤ entryMax A) ∧
      ∃ i j, entryMax A = |A i j| := by sorry

theorem all_entries_bound_three (A : Mat 3) (hA : A.det ≠ 0)
    (path : PivotPath 3) (hp : AdmissiblePath A path) :
    ∀ k i j : Fin 3, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ 3 * entryMax A := by sorry

theorem all_entries_bound_four (A : Mat 4) (hA : A.det ≠ 0)
    (path : PivotPath 4) (hp : AdmissiblePath A path) :
    ∀ k i j : Fin 4, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ (14/3 : ℝ) * entryMax A := by sorry

theorem witness_three :
    witness3.det = 3 ∧ entryMax witness3 = 1 ∧
      AdmissiblePath witness3 (noSwapPath 3) ∧
      growth witness3 (noSwapPath 3) = 3 := by sorry

theorem witness_four :
    witness4.det = (70/9 : ℝ) ∧ entryMax witness4 = 1 ∧
      AdmissiblePath witness4 (noSwapPath 4) ∧
      growth witness4 (noSwapPath 4) = (14/3 : ℝ) := by sorry

theorem greatest_growth_three : IsGreatest (growthSet 3) 3 := by sorry

theorem greatest_growth_four : IsGreatest (growthSet 4) (14/3 : ℝ) := by sorry

theorem exact_rook_growth :
    rookGrowthSup 3 = 3 ∧ rookGrowthSup 4 = (14/3 : ℝ) := by sorry

end NLA.IE15

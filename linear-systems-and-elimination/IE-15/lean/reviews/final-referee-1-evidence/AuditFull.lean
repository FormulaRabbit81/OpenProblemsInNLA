import Solution

set_option autoImplicit false
noncomputable section
open NLA.IE15

example {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, |A i j| ≤ entryMax A) ∧
      ∃ i j, entryMax A = |A i j| := NLA.IE15.entryMax_semantics hn A

example (A : Mat 3) (hA : A.det ≠ 0)
    (path : PivotPath 3) (hp : AdmissiblePath A path) :
    ∀ k i j : Fin 3, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ 3 * entryMax A := NLA.IE15.all_entries_bound_three A hA path hp

example (A : Mat 4) (hA : A.det ≠ 0)
    (path : PivotPath 4) (hp : AdmissiblePath A path) :
    ∀ k i j : Fin 4, k ≤ i → k ≤ j →
      |trajectory A path k.val i j| ≤ (14/3 : ℝ) * entryMax A := NLA.IE15.all_entries_bound_four A hA path hp

example :
    witness3.det = 3 ∧ entryMax witness3 = 1 ∧
      AdmissiblePath witness3 (noSwapPath 3) ∧
      growth witness3 (noSwapPath 3) = 3 := NLA.IE15.witness_three

example :
    witness4.det = (70/9 : ℝ) ∧ entryMax witness4 = 1 ∧
      AdmissiblePath witness4 (noSwapPath 4) ∧
      growth witness4 (noSwapPath 4) = (14/3 : ℝ) := NLA.IE15.witness_four

example : IsGreatest (growthSet 3) 3 := NLA.IE15.greatest_growth_three

example : IsGreatest (growthSet 4) (14/3 : ℝ) := NLA.IE15.greatest_growth_four

example :
    rookGrowthSup 3 = 3 ∧ rookGrowthSup 4 = (14/3 : ℝ) := NLA.IE15.exact_rook_growth


#print axioms NLA.IE15.entryMax_semantics
#assert_trust kernel NLA.IE15.entryMax_semantics
#print axioms NLA.IE15.all_entries_bound_three
#assert_trust kernel NLA.IE15.all_entries_bound_three
#print axioms NLA.IE15.all_entries_bound_four
#assert_trust kernel NLA.IE15.all_entries_bound_four
#print axioms NLA.IE15.witness_three
#assert_trust kernel NLA.IE15.witness_three
#print axioms NLA.IE15.witness_four
#assert_trust kernel NLA.IE15.witness_four
#print axioms NLA.IE15.greatest_growth_three
#assert_trust kernel NLA.IE15.greatest_growth_three
#print axioms NLA.IE15.greatest_growth_four
#assert_trust kernel NLA.IE15.greatest_growth_four
#print axioms NLA.IE15.exact_rook_growth
#assert_trust kernel NLA.IE15.exact_rook_growth
#print axioms NLA.IE15.four_le_fourteen_thirds
#assert_trust kernel NLA.IE15.four_le_fourteen_thirds
#print axioms NLA.IE15.exists_noSwap_representative
#assert_trust kernel NLA.IE15.exists_noSwap_representative
#print axioms NLA.IE15.exists_normalized_noSwap
#assert_trust kernel NLA.IE15.exists_normalized_noSwap
#print axioms NLA.IE15.normalized_final_pivot_three
#assert_trust kernel NLA.IE15.normalized_final_pivot_three
#print axioms NLA.IE15.normalized_final_pivot_four
#assert_trust kernel NLA.IE15.normalized_final_pivot_four
#print axioms NLA.IE15.all_entries_bound_from_normalized
#assert_trust kernel NLA.IE15.all_entries_bound_from_normalized

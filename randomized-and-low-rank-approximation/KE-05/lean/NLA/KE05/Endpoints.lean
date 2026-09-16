import NLA.KE05.Definitions

/- The full deterministic parameter interval from George Stepaniants's proof. -/
set_option autoImplicit false
noncomputable section
namespace NLA.KE05

lemma witness_admissible (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4) :
    Admissible (witnessData e) := by
  intro i j hij r s
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    norm_num [witnessData] at * <;> linarith

lemma witness_range_nonempty (e : ℝ) : {x | ∃ i r, x = witnessData e i r}.Nonempty :=
  ⟨2, 0, 0, rfl⟩

lemma witness_range_bounds (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4)
    (x : ℝ) (hx : ∃ i r, x = witnessData e i r) : 0 ≤ x ∧ x ≤ 2 := by
  obtain ⟨i,r,rfl⟩ := hx
  fin_cases i <;> fin_cases r <;> norm_num [witnessData] <;> constructor <;> linarith

lemma witness_lower (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4) :
    lowerEndpoint (witnessData e) = 0 := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun x hx => (witness_range_bounds e he x hx).1⟩ ⟨2, 0, rfl⟩
  · exact le_csInf (witness_range_nonempty e) (fun x hx => (witness_range_bounds e he x hx).1)

lemma witness_upper (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4) :
    upperEndpoint (witnessData e) = 2 := by
  apply le_antisymm
  · exact csSup_le (witness_range_nonempty e) (fun x hx => (witness_range_bounds e he x hx).2)
  · exact le_csSup ⟨2, fun x hx => (witness_range_bounds e he x hx).2⟩ ⟨0, 0, rfl⟩

lemma rootOrder_zero (i : Fin 3) : rootOrder 0 i = i := by
  fin_cases i <;> rfl

lemma witness_gap (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4) :
    crossGap (witnessData e) 0 = 1 := by
  have hb : ∀ x ∈ {x | ∃ i : Fin 3, 1 ≤ i.val ∧ ∃ r s : Fin 2,
      x = |witnessData e 0 r - witnessData e (rootOrder 0 i) s|}, 1 ≤ x := by
    rintro x ⟨i,hi,r,s,rfl⟩
    fin_cases i <;> fin_cases r <;> fin_cases s <;>
      norm_num [rootOrder_zero, witnessData] at * <;> rw [abs_of_nonneg (by linarith)] <;> linarith
  have hm : (1 : ℝ) ∈ {x | ∃ i : Fin 3, 1 ≤ i.val ∧ ∃ r s : Fin 2,
      x = |witnessData e 0 r - witnessData e (rootOrder 0 i) s|} := by
    refine ⟨2, by decide, 0, 1, ?_⟩
    change (1 : ℝ) = |2 - 1|
    norm_num
  exact le_antisymm (csInf_le ⟨1,hb⟩ hm) (le_csInf ⟨1,hm⟩ hb)

 theorem admissibility_and_endpoints_proved (e : ℝ) (he : 0 < e ∧ e < (1 : ℝ) / 4) :
    Admissible (witnessData e) ∧ lowerEndpoint (witnessData e) = 0 ∧
    upperEndpoint (witnessData e) = 2 ∧ crossGap (witnessData e) 0 = 1 :=
  ⟨witness_admissible e he, witness_lower e he, witness_upper e he, witness_gap e he⟩

end NLA.KE05

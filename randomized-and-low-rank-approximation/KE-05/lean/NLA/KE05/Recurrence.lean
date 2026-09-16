import NLA.KE05.Definitions

/- Literal finite recurrence bookkeeping. This verifies the descending and ascending
orders directly, without a commutative matrix-product replacement. -/
set_option autoImplicit false
noncomputable section
namespace NLA.KE05

lemma rootOrder_list {d : ℕ} (k : Fin d) :
    (List.finRange d).map (rootOrder k) = k :: (List.finRange d).erase k := by
  have hl : (k :: (List.finRange d).erase k).length = d := by
    simp only [List.length_cons, List.length_erase_of_mem (List.mem_finRange k), List.length_finRange]
    have hk := k.isLt
    omega
  apply List.ext_getElem
  · simp [hl]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_finRange, rootOrder]
    exact List.getD_eq_getElem _ _ hj

lemma prefix_index_gt {d : ℕ} (i t : Fin d) (j : ℕ)
    (ht : t ∈ (((List.finRange d).drop (i.val+1)).take (j-i.val))) : i < t := by
  have ht' := List.mem_of_mem_take ht
  obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp ht'
  have hv := congrArg Fin.val he
  simp only [List.getElem_drop, List.getElem_finRange, Fin.coe_cast, Fin.val_mk] at hv
  change i.val < t.val
  omega

lemma foldl_eq_of_pointwise {α β : Type*} (xs : List α) (f g : β → α → β)
    (h : ∀ x ∈ xs, ∀ z, f z x = g z x) (z : β) : xs.foldl f z = xs.foldl g z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih (fun y hy => h y (by simp [hy])) _

lemma prefixS_update {b d : ℕ} (L : Data b d) (w : Sample b d) (k i a : Fin d)
    (hats : Fin d → Mat b) (A : Mat b) (j : ℕ) (ha : a ≤ i) :
    prefixS L w k i (Function.update hats a A) j = prefixS L w k i hats j := by
  unfold prefixS
  apply foldl_eq_of_pointwise
  intro t ht S
  have hta : t ≠ a := by
    have hit := prefix_index_gt i t j ht
    exact ne_of_gt (lt_of_le_of_lt ha hit)
  simp only [Function.update_of_ne hta]

private def StateCorrect {b d : ℕ} (L : Data b d) (w : Sample b d) (k i : Fin d)
    (st : RecurrenceState b d) : Prop :=
    st.lastS i = prefixS L w k i st.hat (d-1) ∧
    st.hat i = (omega w (rootOrder k i) * st.lastS i)⁻¹ *
      Matrix.diagonal (L (rootOrder k i)) * (omega w (rootOrder k i) * st.lastS i)

private lemma correct_step_self {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k i : Fin d) (st : RecurrenceState b d) :
    StateCorrect L w k i (recurrenceStep L w k st i) := by
  simp only [StateCorrect, recurrenceStep, Function.update_self]
  rw [prefixS_update L w k i i _ _ _ le_rfl]
  constructor <;> trivial

private lemma correct_step_lower {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k i a : Fin d) (st : RecurrenceState b d) (hai : a < i)
    (h : StateCorrect L w k i st) :
    StateCorrect L w k i (recurrenceStep L w k st a) := by
  have hia : i ≠ a := ne_of_gt hai
  simp only [StateCorrect, recurrenceStep, Function.update_of_ne hia]
  rw [prefixS_update L w k i a _ _ _ hai.le]
  exact h

private lemma correct_foldr {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d)
    (xs : List (Fin d)) (hx : xs.Pairwise (· < ·)) (st : RecurrenceState b d) :
    ∀ i ∈ xs, StateCorrect L w k i
      (xs.foldr (fun i st => recurrenceStep L w k st i) st) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.pairwise_cons] at hx
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact correct_step_self L w k i _
    · exact correct_step_lower L w k i a _ (hx.1 i hi) (ih hx.2 i hi)

theorem initialized_recurrence_contract {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k : Fin d) (st : RecurrenceState b d) (i : Fin d) :
    let result := (List.finRange d).reverse.foldl (recurrenceStep L w k) st
    result.lastS i = prefixS L w k i result.hat (d-1) ∧
    result.hat i = (omega w (rootOrder k i) * result.lastS i)⁻¹ *
      Matrix.diagonal (L (rootOrder k i)) * (omega w (rootOrder k i) * result.lastS i) := by
  have hp : (List.finRange d).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simpa using hab
  have hc := correct_foldr L w k (List.finRange d) hp st i (List.mem_finRange i)
  simpa only [List.foldl_reverse, StateCorrect] using hc

 theorem literal_recurrence_contract_proved {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k i : Fin d) :
    (List.finRange d).map (rootOrder k) = k :: (List.finRange d).erase k ∧
    (recurrence L w k).lastS i = prefixS L w k i (recurrence L w k).hat (d - 1) ∧
    (recurrence L w k).hat i =
      (omega w (rootOrder k i) * (recurrence L w k).lastS i)⁻¹ *
      Matrix.diagonal (L (rootOrder k i)) *
      (omega w (rootOrder k i) * (recurrence L w k).lastS i) := by
  refine ⟨rootOrder_list k, ?_⟩
  have hp : (List.finRange d).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simpa using hab
  have hc := correct_foldr L w k (List.finRange d) hp ⟨fun _ => 0, fun _ => 0⟩ i (List.mem_finRange i)
  simpa only [recurrence, List.foldl_reverse, StateCorrect] using hc

end NLA.KE05

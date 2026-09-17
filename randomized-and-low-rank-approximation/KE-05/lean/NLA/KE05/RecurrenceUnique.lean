import NLA.KE05.Recurrence
set_option autoImplicit false
noncomputable section
namespace NLA.KE05

lemma prefixS_congr_above {b d : ℕ} (L : Data b d) (w : Sample b d) (k i : Fin d)
    (h g : Fin d → Mat b) (j : ℕ) (he : ∀ t, i < t → h t = g t) :
    prefixS L w k i h j = prefixS L w k i g j := by
  unfold prefixS
  apply foldl_eq_of_pointwise
  intro t ht S
  rw [he t (prefix_index_gt i t j ht)]

/-- The literal triangular recurrence equations determine the entire final state,
even with total matrix inverse and without a nonsingularity hypothesis. -/
lemma recurrence_state_unique {b d : ℕ} (L : Data b d) (w : Sample b d) (k : Fin d)
    (A B : RecurrenceState b d)
    (hA : ∀ i, A.lastS i = prefixS L w k i A.hat (d-1) ∧
      A.hat i = (omega w (rootOrder k i) * A.lastS i)⁻¹ *
        Matrix.diagonal (L (rootOrder k i)) * (omega w (rootOrder k i) * A.lastS i))
    (hB : ∀ i, B.lastS i = prefixS L w k i B.hat (d-1) ∧
      B.hat i = (omega w (rootOrder k i) * B.lastS i)⁻¹ *
        Matrix.diagonal (L (rootOrder k i)) * (omega w (rootOrder k i) * B.lastS i)) : A = B := by
  have hh (m : ℕ) : ∀ i : Fin d, d-i.val = m → A.hat i = B.hat i := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i hi
      have hp := prefixS_congr_above L w k i A.hat B.hat (d-1) (fun t ht =>
        ih (d-t.val) (by have := i.isLt; have := t.isLt; change i.val < t.val at ht; omega) t rfl)
      have hs : A.lastS i = B.lastS i := (hA i).1.trans (hp.trans (hB i).1.symm)
      rw [(hA i).2, (hB i).2, hs]
  have hhat : A.hat = B.hat := funext (fun i => hh (d-i.val) i rfl)
  have hlast : A.lastS = B.lastS := by
    funext i
    rw [(hA i).1, (hB i).1, hhat]
  cases A
  cases B
  cases hhat
  cases hlast
  rfl

lemma recurrence_initial_independent {b d : ℕ} (L : Data b d) (w : Sample b d)
    (k : Fin d) (st : RecurrenceState b d) :
    (List.finRange d).reverse.foldl (recurrenceStep L w k) st = recurrence L w k := by
  apply recurrence_state_unique L w k
  · intro i
    exact initialized_recurrence_contract L w k st i
  · intro i
    exact (literal_recurrence_contract_proved L w k i).2

end NLA.KE05

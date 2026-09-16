import NLA.KE05.GenericWitness
import NLA.KE05.IdentityWitness

/- Regularity and the commuting identity witness are propagated through each
actual recurrence step. The initial auxiliary state here is convenient only for
this induction; RecurrenceUnique proves initialization does not affect the result. -/
set_option autoImplicit false
noncomputable section
namespace NLA.KE05

lemma regular_baseBlock {b d : ℕ} (L : Data b d) (k i : Fin d) (r c : Fin b) :
    RegularAt (identitySample b d) (fun w => baseBlock L w k i r c) := by
  apply regular_similarity
  · exact regular_omega _ _
  · rw [omega_identity]
    norm_num

lemma regular_prefixS {b d : ℕ} (L : Data b d) (k i : Fin d)
    (hats : Sample b d → Fin d → Mat b)
    (hh : ∀ t r c, RegularAt (identitySample b d) (fun w => hats w t r c))
    (j : ℕ) (r c : Fin b) :
    RegularAt (identitySample b d) (fun w => prefixS L w k i (hats w) j r c) := by
  have hf : ∀ (xs : List (Fin d)) (A : Sample b d → Mat b),
      (∀ r c, RegularAt (identitySample b d) (fun w => A w r c)) →
      ∀ r c, RegularAt (identitySample b d) (fun w =>
        xs.foldl (fun S t => baseBlock L w k i * S - S * hats w t) (A w) r c) := by
    intro xs
    induction xs with
    | nil => intro A hA; exact hA
    | cons t xs ih =>
      intro A hA
      apply ih (fun w => baseBlock L w k i * A w - A w * hats w t)
      intro r c
      exact (regular_matrix_mul _ _ (regular_baseBlock L k i) hA r c).sub
        (regular_matrix_mul _ _ hA (hh t) r c)
  exact hf _ (fun _ => 1) (fun r c => RegularAt.const _) r c

structure GoodState {b d : ℕ} (L : Data b d) (k : Fin d)
    (st : Sample b d → RecurrenceState b d) : Prop where
  hat_regular : ∀ i r c, RegularAt (identitySample b d) (fun w => (st w).hat i r c)
  last_regular : ∀ i r c, RegularAt (identitySample b d) (fun w => (st w).lastS i r c)
  hat_identity : ∀ i, (st (identitySample b d)).hat i = Matrix.diagonal (L (rootOrder k i))
  last_det_identity : ∀ i, ((st (identitySample b d)).lastS i).det ≠ 0

lemma goodState_step {b d : ℕ} (L : Data b d) (hL : Admissible L) (k i : Fin d)
    (st : Sample b d → RecurrenceState b d) (hst : GoodState L k st) :
    GoodState L k (fun w => recurrenceStep L w k (st w) i) := by
  let S : Sample b d → Mat b := fun w => prefixS L w k i (st w).hat (d-1)
  have hS : ∀ r c, RegularAt (identitySample b d) (fun w => S w r c) :=
    regular_prefixS L k i (fun w => (st w).hat) hst.hat_regular (d-1)
  obtain ⟨v,hv,hv0⟩ := prefixS_identity_diagonal L hL k i
    (st (identitySample b d)).hat hst.hat_identity (d-1)
  have hS0 : (S (identitySample b d)).det ≠ 0 := by
    dsimp only [S]
    rw [hv]
    exact diagonal_nonzero_det v hv0
  let O : Sample b d → Mat b := fun w => omega w (rootOrder k i) * S w
  have hO : ∀ r c, RegularAt (identitySample b d) (fun w => O w r c) :=
    regular_matrix_mul _ _ (regular_omega _ _) hS
  have hO0 : (O (identitySample b d)).det ≠ 0 := by simpa [O, omega_identity] using hS0
  constructor
  · intro t r c
    by_cases ht : t = i
    · subst t
      simpa only [recurrenceStep, Function.update_self] using
        regular_similarity O hO hO0 (L (rootOrder k i)) r c
    · simpa only [recurrenceStep, Function.update_of_ne ht] using hst.hat_regular t r c
  · intro t r c
    by_cases ht : t = i
    · subst t
      simpa only [recurrenceStep, Function.update_self] using hS r c
    · simpa only [recurrenceStep, Function.update_of_ne ht] using hst.last_regular t r c
  · intro t
    by_cases ht : t = i
    · subst t
      simp only [recurrenceStep, Function.update_self, omega_identity, Matrix.one_mul]
      rw [hv]
      exact diagonal_similar v (L (rootOrder k i)) hv0
    · simpa only [recurrenceStep, Function.update_of_ne ht] using hst.hat_identity t
  · intro t
    by_cases ht : t = i
    · subst t
      simpa only [recurrenceStep, Function.update_self] using hS0
    · simpa only [recurrenceStep, Function.update_of_ne ht] using hst.last_det_identity t

 def convenientState {b d : ℕ} (L : Data b d) (k : Fin d) : RecurrenceState b d :=
  ⟨fun i => Matrix.diagonal (L (rootOrder k i)), fun _ => 1⟩

lemma goodState_initial {b d : ℕ} (L : Data b d) (k : Fin d) :
    GoodState L k (fun _ => convenientState L k) := by
  constructor
  · intro i r c; exact RegularAt.const _
  · intro i r c; exact RegularAt.const _
  · intro i; rfl
  · intro i; simp [convenientState]

lemma goodState_fold {b d : ℕ} (L : Data b d) (hL : Admissible L) (k : Fin d)
    (xs : List (Fin d)) (st : Sample b d → RecurrenceState b d) (hst : GoodState L k st) :
    GoodState L k (fun w => xs.foldl (recurrenceStep L w k) (st w)) := by
  induction xs generalizing st with
  | nil => exact hst
  | cons i xs ih =>
    exact ih (fun w => recurrenceStep L w k (st w) i) (goodState_step L hL k i st hst)

end NLA.KE05

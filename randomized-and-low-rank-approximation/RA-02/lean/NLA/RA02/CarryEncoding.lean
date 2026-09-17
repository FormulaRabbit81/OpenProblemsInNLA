/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Exact binary-history encoding in the original label space. At each stage the
carry and new ordinary label are the two unselected activated labels; future
ordinary labels also remain unselected. No binary history is enumerated.
-/
import NLA.RA02.HistoryLabels
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section

lemma carryLabel_bounds (r : ℕ) (bits : Fin r → Bool) (s : ℕ) (hs : s ≤ r) :
    carryLabel r bits s = Fin.last r ∨ (carryLabel r bits s).val < s := by
  revert hs
  induction s with
  | zero =>
      intro _
      exact Or.inl rfl
  | succ s ih =>
      intro hs
      have hsr : s < r := Nat.lt_of_lt_of_le (Nat.lt_succ_self s) hs
      cases hb : bits ⟨s, hsr⟩
      · simp only [carryLabel, dif_pos hsr, hb, Bool.false_eq_true, ↓reduceIte]
        rcases ih (Nat.le_of_lt hsr) with hc | hc
        · exact Or.inl hc
        · exact Or.inr (Nat.lt.step hc)
      · simp only [carryLabel, dif_pos hsr, hb, ↓reduceIte]
        exact Or.inr (Nat.lt_succ_self s)

lemma carryLabel_mem_initialLabels (r : ℕ) (bits : Fin r → Bool) (s : ℕ)
    (hs : s ≤ r) : carryLabel r bits s ∈ initialLabels r s := by
  rcases carryLabel_bounds r bits s hs with hc | hc
  · simp [initialLabels, hc]
  · simp [initialLabels, hc]

lemma carryLabel_ne_next (r : ℕ) (bits : Fin r → Bool) (s : Fin r) :
    carryLabel r bits s.val ≠ s.castSucc := by
  rcases carryLabel_bounds r bits s.val (Nat.le_of_lt s.isLt) with hc | hc
  · rw [hc]
    exact (Fin.castSucc_ne_last s).symm
  · intro heq
    have hval := congrArg Fin.val heq
    change (carryLabel r bits s.val).val = s.val at hval
    omega

lemma carryLabel_step (r : ℕ) (bits : Fin r → Bool) (s : Fin r) :
    carryLabel r bits (s.val + 1) =
      if bits s then s.castSucc else carryLabel r bits s.val := by
  rw [carryLabel, dif_pos s.isLt]

lemma retainedPrefix_length (r : ℕ) (bits : Fin r → Bool) (s : ℕ) (hs : s ≤ r) :
    (retainedPrefix r bits s).length = s := by
  simp only [retainedPrefix, List.length_take, List.length_ofFn, Nat.min_eq_left hs]

lemma retainedPrefix_full (r : ℕ) (bits : Fin r → Bool) :
    retainedPrefix r bits r = List.ofFn (retainedHistory r bits) := by
  unfold retainedPrefix
  apply List.take_of_length_le
  simp only [List.length_ofFn, le_refl]

lemma retainedPrefix_succ (r : ℕ) (bits : Fin r → Bool) (s : ℕ) (hs : s < r) :
    retainedPrefix r bits (s + 1) =
      retainedPrefix r bits s ++ [retainedHistory r bits ⟨s, hs⟩] := by
  unfold retainedPrefix
  have hlen : s < (List.ofFn (retainedHistory r bits)).length := by
    simpa only [List.length_ofFn] using hs
  rw [List.take_succ_eq_append_getElem hlen]
  exact congrArg (fun a => (List.ofFn (retainedHistory r bits)).take s ++ [a])
    (List.getElem_ofFn hlen)

lemma initialLabels_zero (r : ℕ) : initialLabels r 0 = {Fin.last r} := by
  ext j
  simp [initialLabels]

lemma next_not_mem_initialLabels (r : ℕ) (s : Fin r) :
    s.castSucc ∉ initialLabels r s.val := by
  simp [initialLabels]

lemma initialLabels_succ (r : ℕ) (s : ℕ) (hs : s < r) :
    initialLabels r (s + 1) = insert (⟨s, hs⟩ : Fin r).castSucc (initialLabels r s) := by
  ext j
  have heq : j = (⟨s, hs⟩ : Fin r).castSucc ↔ j.val = s := by
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      exact Fin.ext h
  simp only [initialLabels, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, heq]
  omega

lemma retained_prefix_set (r : ℕ) (bits : Fin r → Bool) (s : ℕ) (hs : s ≤ r) :
    (retainedPrefix r bits s).toFinset = (initialLabels r s).erase (carryLabel r bits s) := by
  revert hs
  induction s with
  | zero =>
      intro _
      simp [retainedPrefix, initialLabels_zero, carryLabel]
  | succ s ih =>
      intro hs
      have hsr : s < r := Nat.lt_of_lt_of_le (Nat.lt_succ_self s) hs
      have hsingle : ([retainedHistory r bits ⟨s, hsr⟩] : List (Fin (r + 1))).toFinset =
          {retainedHistory r bits ⟨s, hsr⟩} := by simp
      rw [retainedPrefix_succ r bits s hsr, List.toFinset_append, hsingle,
        Finset.union_singleton, ih (Nat.le_of_lt hsr), initialLabels_succ r s hsr,
        carryLabel_step r bits ⟨s, hsr⟩]
      cases hb : bits ⟨s, hsr⟩
      · simp only [retainedHistory, hb, Bool.false_eq_true, ↓reduceIte]
        exact (Finset.erase_insert_of_ne (carryLabel_ne_next r bits ⟨s, hsr⟩).symm).symm
      · simp only [retainedHistory, hb, ↓reduceIte]
        rw [Finset.insert_erase (carryLabel_mem_initialLabels r bits s (Nat.le_of_lt hsr)),
          Finset.erase_insert (next_not_mem_initialLabels r ⟨s, hsr⟩)]

lemma retainedHistory_not_mem_prefix (r : ℕ) (bits : Fin r → Bool) (s : Fin r) :
    retainedHistory r bits s ∉ retainedPrefix r bits s.val := by
  intro hmem
  have hset := List.mem_toFinset.mpr hmem
  rw [retained_prefix_set r bits s.val (Nat.le_of_lt s.isLt)] at hset
  cases hb : bits s
  · have hnext : s.castSucc ∈
        (initialLabels r s.val).erase (carryLabel r bits s.val) := by
      simpa only [retainedHistory, hb, Bool.false_eq_true, ↓reduceIte] using hset
    exact next_not_mem_initialLabels r s (Finset.mem_erase.mp hnext).2
  · have hcarry : carryLabel r bits s.val ∈
        (initialLabels r s.val).erase (carryLabel r bits s.val) := by
      simpa only [retainedHistory, hb, ↓reduceIte] using hset
    exact (Finset.mem_erase.mp hcarry).1 rfl

lemma retainedPrefix_nodup (r : ℕ) (bits : Fin r → Bool) (s : ℕ) (hs : s ≤ r) :
    (retainedPrefix r bits s).Nodup := by
  revert hs
  induction s with
  | zero =>
      intro _
      simp [retainedPrefix]
  | succ s ih =>
      intro hs
      have hsr : s < r := Nat.lt_of_lt_of_le (Nat.lt_succ_self s) hs
      rw [retainedPrefix_succ r bits s hsr]
      apply List.nodup_append.mpr
      refine ⟨ih (Nat.le_of_lt hsr), by simp, ?_⟩
      intro a ha b hb hab
      have hb' : b = retainedHistory r bits ⟨s, hsr⟩ := by simpa using hb
      exact retainedHistory_not_mem_prefix r bits ⟨s, hsr⟩ ((hab.trans hb') ▸ ha)

lemma retainedHistory_bit_recovery (r : ℕ) (bits : Fin r → Bool) (s : Fin r) :
    retainedHistory r bits s = s.castSucc ↔ bits s = false := by
  cases hb : bits s <;> simp [retainedHistory, hb, carryLabel_ne_next r bits s]

lemma retainedHistory_injective (r : ℕ) : Function.Injective (retainedHistory r) := by
  intro bits₁ bits₂ h
  funext s
  have hsame : bits₁ s = false ↔ bits₂ s = false := by
    rw [← retainedHistory_bit_recovery r bits₁ s,
      ← retainedHistory_bit_recovery r bits₂ s, h]
  cases h₁ : bits₁ s <;> cases h₂ : bits₂ s <;> simp_all

theorem retained_history_count (r : ℕ) :
    Function.Injective (retainedHistory r) ∧ (retainedHistories r).card = 2 ^ r ∧
    ∀ bits : Fin r → Bool, (List.ofFn (retainedHistory r bits)).Nodup := by
  refine ⟨retainedHistory_injective r, ?_, ?_⟩
  · rw [retainedHistories, Finset.card_image_of_injective _ (retainedHistory_injective r)]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  · intro bits
    simpa only [retainedPrefix_full] using retainedPrefix_nodup r bits r (le_refl r)

theorem retained_prefix_description (r : ℕ) (bits : Fin r → Bool) (s : ℕ) (hs : s ≤ r) :
    (carryLabel r bits s = Fin.last r ∨ (carryLabel r bits s).val < s) ∧
    (retainedPrefix r bits s).toFinset = (initialLabels r s).erase (carryLabel r bits s) := by
  exact ⟨carryLabel_bounds r bits s hs, retained_prefix_set r bits s hs⟩

#print axioms retained_history_count
#assert_trust kernel retained_history_count
#print axioms retained_prefix_description
#assert_trust kernel retained_prefix_description

end
end NLA.RA02

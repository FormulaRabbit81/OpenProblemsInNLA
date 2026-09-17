/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Actual unused-label and full residual-state identities for every encoded
prefix, including the empty and terminal prefixes. No trace estimate is assumed.
-/
import NLA.RA02.CarryEncoding
import NLA.RA02.DistinctHistory

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section

def futureOrdinary (r s : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => s ≤ i.val)

@[simp] lemma mem_futureOrdinary (r s : ℕ) (i : Fin r) :
    i ∈ futureOrdinary r s ↔ s ≤ i.val := by
  simp [futureOrdinary]

lemma retained_remaining_when_last (r : ℕ) (bits : Fin r → Bool) (s : ℕ)
    (hs : s ≤ r) (hc : carryLabel r bits s = Fin.last r) :
    lastRemaining r (retainedPrefix r bits s) = true ∧
      remainingOrdinary r (retainedPrefix r bits s) = futureOrdinary r s := by
  have hlast : Fin.last r ∉ retainedPrefix r bits s := by
    intro hmem
    have hset := List.mem_toFinset.mpr hmem
    rw [retained_prefix_set r bits s hs, hc] at hset
    exact (Finset.mem_erase.mp hset).1 rfl
  refine ⟨lastRemaining_of_not_mem r _ hlast, ?_⟩
  ext i
  have hmem : i.castSucc ∈ retainedPrefix r bits s ↔ i.val < s := by
    rw [← List.mem_toFinset, retained_prefix_set r bits s hs, hc]
    simp [initialLabels]
  simp only [mem_remainingOrdinary, mem_futureOrdinary, hmem, not_lt]

lemma retained_remaining_when_ordinary (r : ℕ) (bits : Fin r → Bool) (s : ℕ)
    (hs : s ≤ r) (j : Fin r) (hc : carryLabel r bits s = j.castSucc) :
    j.val < s ∧ lastRemaining r (retainedPrefix r bits s) = false ∧
      remainingOrdinary r (retainedPrefix r bits s) = insert j (futureOrdinary r s) := by
  have hj : j.val < s := by
    rcases carryLabel_bounds r bits s hs with hlast | hsmall
    · exact False.elim (Fin.castSucc_ne_last j (hc.symm.trans hlast))
    · rw [hc] at hsmall
      exact hsmall
  have hlast : Fin.last r ∈ retainedPrefix r bits s := by
    rw [← List.mem_toFinset, retained_prefix_set r bits s hs, hc]
    simp [initialLabels, Ne.symm (Fin.castSucc_ne_last j)]
  refine ⟨hj, ?_, ?_⟩
  · simp [lastRemaining, List.contains_eq_mem, hlast]
  · ext i
    have hmem : i.castSucc ∈ retainedPrefix r bits s ↔ i ≠ j ∧ i.val < s := by
      rw [← List.mem_toFinset, retained_prefix_set r bits s hs, hc]
      simp [initialLabels]
    simp only [mem_remainingOrdinary, hmem, Finset.mem_insert, mem_futureOrdinary]
    by_cases hij : i = j <;> simp [hij, not_lt]

lemma retained_carry_cases (r : ℕ) (bits : Fin r → Bool) (s : ℕ) (hs : s ≤ r) :
    carryLabel r bits s = Fin.last r ∨
      ∃ j : Fin r, j.val < s ∧ carryLabel r bits s = j.castSucc := by
  rcases carryLabel_bounds r bits s hs with hlast | hsmall
  · exact Or.inl hlast
  · right
    refine ⟨⟨(carryLabel r bits s).val, hsmall.trans_le hs⟩, hsmall, ?_⟩
    exact Fin.ext rfl

lemma retained_residual_when_last (r : ℕ) (bits : Fin r → Bool) (s : ℕ)
    (hs : s ≤ r) (hc : carryLabel r bits s = Fin.last r) :
    pathResidual (arrowhead r) (retainedPrefix r bits s) =
      arrowheadState r (futureOrdinary r s) true := by
  have hremaining := retained_remaining_when_last r bits s hs hc
  rw [pathResidual_distinct_state r _ (retainedPrefix_nodup r bits s hs),
    hremaining.1, hremaining.2]

lemma retained_residual_when_ordinary (r : ℕ) (bits : Fin r → Bool) (s : ℕ)
    (hs : s ≤ r) (j : Fin r) (hc : carryLabel r bits s = j.castSucc) :
    pathResidual (arrowhead r) (retainedPrefix r bits s) =
      arrowheadState r (insert j (futureOrdinary r s)) false := by
  have hremaining := retained_remaining_when_ordinary r bits s hs j hc
  rw [pathResidual_distinct_state r _ (retainedPrefix_nodup r bits s hs),
    hremaining.2.1, hremaining.2.2]

#print axioms retained_residual_when_last
#assert_trust kernel retained_residual_when_last
#print axioms retained_residual_when_ordinary
#assert_trust kernel retained_residual_when_ordinary

end
end NLA.RA02

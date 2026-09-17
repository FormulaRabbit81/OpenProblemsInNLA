/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Exact changes to the frozen active-label and distinguished-label definitions.
These identities use arbitrary chronological lists, not binary retained paths.
-/
import NLA.RA02.ArrowheadEntries
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

@[simp] lemma remainingOrdinary_nil (r : ℕ) :
    remainingOrdinary r [] = Finset.univ := by
  ext i
  simp [remainingOrdinary]

@[simp] lemma lastRemaining_nil (r : ℕ) : lastRemaining r [] = true := by
  simp [lastRemaining]

@[simp] lemma mem_remainingOrdinary (r : ℕ) (w : List (Fin (r + 1))) (i : Fin r) :
    i ∈ remainingOrdinary r w ↔ i.castSucc ∉ w := by
  simp [remainingOrdinary]

lemma remainingOrdinary_append_ordinary (r : ℕ) (w : List (Fin (r + 1))) (i : Fin r) :
    remainingOrdinary r (w ++ [i.castSucc]) = (remainingOrdinary r w).erase i := by
  ext j
  simp [remainingOrdinary, Finset.mem_erase, Fin.castSucc_inj, and_comm]

lemma remainingOrdinary_append_last (r : ℕ) (w : List (Fin (r + 1))) :
    remainingOrdinary r (w ++ [Fin.last r]) = remainingOrdinary r w := by
  ext i
  simp [remainingOrdinary]

lemma lastRemaining_append_ordinary (r : ℕ) (w : List (Fin (r + 1))) (i : Fin r) :
    lastRemaining r (w ++ [i.castSucc]) = lastRemaining r w := by
  simp [lastRemaining, List.contains_eq_mem]

lemma lastRemaining_append_last (r : ℕ) (w : List (Fin (r + 1))) :
    lastRemaining r (w ++ [Fin.last r]) = false := by
  simp [lastRemaining, List.contains_eq_mem]

lemma lastRemaining_of_not_mem (r : ℕ) (w : List (Fin (r + 1)))
    (h : Fin.last r ∉ w) : lastRemaining r w = true := by
  simp [lastRemaining, List.contains_eq_mem, h]

#print axioms remainingOrdinary_append_ordinary
#assert_trust kernel remainingOrdinary_append_ordinary
#print axioms lastRemaining_append_ordinary
#assert_trust kernel lastRemaining_append_ordinary

end
end NLA.RA02

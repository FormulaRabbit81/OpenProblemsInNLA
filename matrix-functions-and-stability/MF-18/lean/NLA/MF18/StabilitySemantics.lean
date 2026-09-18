/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

This semantics bridge uses the finite algebraic spectrum directly, so it
introduces no alternate matrix norm or operator topology.
-/
import NLA.MF18.Definitions
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped ENNReal

noncomputable section
namespace NLA.MF18

theorem stability_semantics {n : ℕ} [NeZero n] (S : Mat n) :
    StrictStable S ↔ spectralRadius ℂ S < 1 := by
  constructor
  · intro hs
    obtain ⟨z, hz⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ S
    unfold spectralRadius
    apply (S.finite_spectrum.ciSup_lt_iff ⟨z, hz, by simp⟩).mpr
    intro lam hlam
    have hnorm := hs lam (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hlam)
    exact_mod_cast hnorm
  · intro hs lam hlam
    have hspec : lam ∈ spectrum ℂ S := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hlam
    have hle : (‖lam‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ S := by
      unfold spectralRadius
      exact le_iSup₂ (α := ℝ≥0∞) lam hspec
    exact_mod_cast hle.trans_lt hs

#print axioms stability_semantics

end NLA.MF18

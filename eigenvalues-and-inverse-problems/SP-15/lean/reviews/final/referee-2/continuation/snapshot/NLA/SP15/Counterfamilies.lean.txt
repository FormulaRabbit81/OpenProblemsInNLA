/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

Arbitrarily large finite families in dimension nine have identical singular
values after every complex shift and are pairwise unitarily inequivalent.
The final theorem negates the literal canonical finiteness statement.
-/
import NLA.SP15.FiniteFiber
import NLA.SP15.ShiftedSpectrum
import NLA.SP15.UnitaryInjectivity

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section

theorem arbitrary_finite_counterfamilies (M : ℕ) :
    ∃ A : Fin (M + 1) → Square 9,
      (∀ i j, SuperIdentical (A i) (A j)) ∧
      ∀ i j : Fin (M + 1), i < j → ¬ UnitarySimilar (A i) (A j) := by
  obtain ⟨x, hinj, hbox, hcoeff⟩ := finite_fiber_selection M
  refine ⟨fun i => constructedMatrix (x i), ?_, ?_⟩
  · intro i j
    exact equal_coefficients_shifted_singular_values (x i) (x j) (hbox i) (hbox j)
      ((hcoeff i).trans (hcoeff j).symm)
  · intro i j hij hU
    exact (ne_of_lt hij) (hinj (constructed_unitary_injectivity (x i) (x j)
      (hbox i) (hbox j) hU))

theorem canonical_finiteness_false : ¬ CanonicalFiniteness := by
  intro h
  obtain ⟨M, _, hM⟩ := h 9 (by decide)
  obtain ⟨A, hA, hNo⟩ := arbitrary_finite_counterfamilies M
  obtain ⟨i, j, hij, hU⟩ := hM A hA
  exact hNo i j hij hU

#print axioms arbitrary_finite_counterfamilies
#assert_trust kernel arbitrary_finite_counterfamilies
#print axioms canonical_finiteness_false
#assert_trust kernel canonical_finiteness_false

end
end NLA.SP15

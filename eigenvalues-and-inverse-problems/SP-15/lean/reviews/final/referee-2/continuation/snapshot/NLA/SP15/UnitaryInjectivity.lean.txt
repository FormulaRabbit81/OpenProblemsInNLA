/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.
-/
import NLA.SP15.MiddleConjugacy
import NLA.SP15.SliceRigidity

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section

theorem constructed_unitary_injectivity (x y : Parameters)
    (hx : x ∈ parameterBox) (hy : y ∈ parameterBox)
    (h : UnitarySimilar (constructedMatrix x) (constructedMatrix y)) : x = y := by
  obtain ⟨V, hV, hP, hQ⟩ := middle_block_conjugacy x y hx hy h
  exact parameter_slice_rigidity x y hx hy V hV hP hQ

#print axioms constructed_unitary_injectivity
#assert_trust kernel constructed_unitary_injectivity

end
end NLA.SP15

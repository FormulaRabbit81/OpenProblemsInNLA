/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.
-/
import NLA.SP15.GramPolynomial
import NLA.SP15.GramSemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section

theorem equal_coefficients_shifted_singular_values (x y : Parameters)
    (hx : x ∈ parameterBox) (hy : y ∈ parameterBox)
    (hxy : coefficients x = coefficients y) :
    SuperIdentical (constructedMatrix x) (constructedMatrix y) := by
  intro z k
  exact gram_charpoly_singular_values
    (constructedMatrix x - z • (1 : Square 9))
    (constructedMatrix y - z • (1 : Square 9))
    (equal_coefficients_gram_charpoly x y hx hy hxy z) k.val

#print axioms equal_coefficients_shifted_singular_values
#assert_trust kernel equal_coefficients_shifted_singular_values

end
end NLA.SP15

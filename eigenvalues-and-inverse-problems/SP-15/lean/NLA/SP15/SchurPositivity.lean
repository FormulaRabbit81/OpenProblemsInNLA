/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

The pivots are positive by scalar positivity and the proved whole-box
positivity. No spectral calculation or quantitative inverse estimate is used.
-/
import NLA.SP15.SquareRoots

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder

theorem schur_positive_blocks (x : Parameters) (hx : x ∈ parameterBox)
    (z : ℂ) (t : ℝ) (ht : 0 < t) :
    0 < shiftScalar z t ∧
    (((shiftScalar z t : ℝ) : ℂ) • (1 : Square 3)).PosDef ∧
    (schurPivot x z t).PosDef := by
  have hs : 0 < shiftScalar z t := add_pos_of_pos_of_nonneg ht (Complex.normSq_nonneg z)
  have hone : (1 : Square 3).PosDef := Matrix.PosDef.one
  have hscalar := hone.smul (Complex.zero_lt_real.mpr hs)
  have hsquare := hone.smul (Complex.zero_lt_real.mpr (sq_pos_of_pos hs))
  have hP := (parameter_matrices_positive x hx).1.smul (Complex.zero_lt_real.mpr ht)
  exact ⟨hs, hscalar, hsquare.add hP⟩

#print axioms schur_positive_blocks
#assert_trust kernel schur_positive_blocks

end
end NLA.SP15

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

The same 1/16 box works for positivity and coordinate separation. Complex
norms use Mathlib's real/imaginary bound; no square-root enclosure is needed.
-/
import NLA.SP15.Numerical
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix Topology

private theorem coordinate_bounds (x : Parameters) (hx : x ∈ parameterBox)
    (i : Fin 10) : basePoint i - boxRadius < x i ∧ x i < basePoint i + boxRadius := by
  have hi := abs_lt.mp (hx i)
  constructor <;> linarith [hi.1, hi.2]

theorem parameter_box_geometry : IsOpen parameterBox ∧ basePoint ∈ parameterBox := by
  constructor
  · -- The frozen box is the finite intersection of these open coordinate conditions.
    change IsOpen {x : Parameters | ∀ i, |x i - basePoint i| < boxRadius}
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hcoord : Continuous (fun x : Parameters => x i - basePoint i) :=
      (continuous_apply i).sub continuous_const
    simpa only [Real.norm_eq_abs] using
      (isOpen_lt hcoord.norm continuous_const)
  · intro i
    simpa using box_scalar_certificate.1

theorem parameter_box_bounds (x : Parameters) (hx : x ∈ parameterBox) :
    (∀ i : Fin 3, 0 < pCoordinates x i) ∧ 0 < x 6 ∧ 0 < x 7 ∧
    ∀ i : Fin 3,
      (∑ j ∈ Finset.univ.erase i, ‖qMatrix x i j‖) + 3 / 4 < (qMatrix x i i).re := by
  have hsmall : 0 < 1 - boxRadius := box_scalar_certificate.2.1
  have hlarge : 0 < 1 + boxRadius := by linarith [box_scalar_certificate.1]
  have hmargin := box_scalar_certificate.2.2.2.2
  have hone (i : Fin 10) (hi : basePoint i = 1) :
      0 < x i ∧ |x i| < 1 + boxRadius := by
    have h := coordinate_bounds x hx i
    rw [hi] at h
    have hpos : 0 < x i := lt_trans hsmall h.1
    exact ⟨hpos, by simpa only [abs_of_pos hpos] using h.2⟩
  have h6 := hone 6 (by rfl)
  have h7 := hone 7 (by rfl)
  have h8 := hone 8 (by rfl)
  have h9 := hone 9 (by rfl)
  have hp0 := coordinate_bounds x hx 0
  have hp1 := coordinate_bounds x hx 1
  have hp2 := coordinate_bounds x hx 2
  -- Reduce the fixed center vector before any real linear arithmetic.
  dsimp only [basePoint, Matrix.cons_val] at hp0 hp1 hp2
  have hp : ∀ i : Fin 3, 0 < pCoordinates x i := by
    intro i
    -- Each fixed p coordinate is the corresponding original real parameter.
    fin_cases i
    · change 0 < x 0
      linarith [hp0.1]
    · change 0 < x 1
      linarith [hp1.1]
    · change 0 < x 2
      linarith [hp2.1]
  have hplus : ‖(x 8 : ℂ) + Complex.I * (x 9 : ℂ)‖ < 2 * (1 + boxRadius) := by
    have h : ‖(x 8 : ℂ) + Complex.I * (x 9 : ℂ)‖ ≤ |x 8| + |x 9| := by
      simpa using Complex.norm_le_abs_re_add_abs_im ((x 8 : ℂ) + Complex.I * (x 9 : ℂ))
    linarith [h8.2, h9.2]
  have hminus : ‖(x 8 : ℂ) - Complex.I * (x 9 : ℂ)‖ < 2 * (1 + boxRadius) := by
    have h : ‖(x 8 : ℂ) - Complex.I * (x 9 : ℂ)‖ ≤ |x 8| + |x 9| := by
      simpa using Complex.norm_le_abs_re_add_abs_im ((x 8 : ℂ) - Complex.I * (x 9 : ℂ))
    linarith [h8.2, h9.2]
  refine ⟨hp, h6.1, h7.1, ?_⟩
  intro i
  have hrow : (∑ j ∈ Finset.univ.erase i, ‖qMatrix x i j‖) <
      3 * (1 + boxRadius) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    fin_cases i <;>
      simp [Fin.sum_univ_succ, qMatrix, Complex.norm_real, Real.norm_eq_abs] <;>
      linarith [h6.2, h7.2]
  have hdiag : 4 - boxRadius < (qMatrix x i i).re := by
    have h3 := (coordinate_bounds x hx 3).1
    have h4 := (coordinate_bounds x hx 4).1
    have h5 := (coordinate_bounds x hx 5).1
    fin_cases i
    · simpa [basePoint, qMatrix] using h3
    · simpa [basePoint, qMatrix] using h4
    · simpa [basePoint, qMatrix] using h5
  linarith

theorem p_intervals_separate (x y : Parameters) (hx : x ∈ parameterBox)
    (hy : y ∈ parameterBox) (i j : Fin 3) (hij : i ≠ j) :
    pCoordinates x i ≠ pCoordinates y j := by
  have hgap := box_scalar_certificate.2.2.1
  have hx0 := coordinate_bounds x hx 0
  have hx1 := coordinate_bounds x hx 1
  have hx2 := coordinate_bounds x hx 2
  have hy0 := coordinate_bounds y hy 0
  have hy1 := coordinate_bounds y hy 1
  have hy2 := coordinate_bounds y hy 2
  dsimp only [basePoint, Matrix.cons_val] at hx0 hx1 hx2 hy0 hy1 hy2
  intro h
  fin_cases i <;> fin_cases j <;> simp [pCoordinates] at h hij <;> linarith

#print axioms parameter_box_geometry
#assert_trust kernel parameter_box_geometry
#print axioms parameter_box_bounds
#assert_trust kernel parameter_box_bounds
#print axioms p_intervals_separate
#assert_trust kernel p_intervals_separate

end
end NLA.SP15

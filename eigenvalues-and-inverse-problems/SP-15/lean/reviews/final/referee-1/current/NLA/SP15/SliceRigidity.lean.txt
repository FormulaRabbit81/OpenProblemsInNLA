/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Fortier Bourque and Ransford retain
credit for the original question and generic finiteness theorem.

Cross-point interval separation fixes every diagonal position. The two
strictly positive connecting entries then fix the relative complex phases.
All ten original parameters are recovered from the actual matrix entries.
-/
import NLA.SP15.BoxGeometry
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP15
noncomputable section
open scoped BigOperators Matrix

private theorem diagonal_conjugacy_entry (v : Fin 3 → ℂ) (A : Square 3)
    (i j : Fin 3) :
    ((Matrix.diagonal v).conjTranspose * A * Matrix.diagonal v) i j =
      star (v i) * A i j * v j := by
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply]

private theorem separated_unitary_diagonal (x y : Parameters)
    (hx : x ∈ parameterBox) (hy : y ∈ parameterBox) (V : Square 3)
    (hV : V.conjTranspose * V = 1)
    (hP : pMatrix y = V.conjTranspose * pMatrix x * V) :
    ∃ v : Fin 3 → ℂ, V = Matrix.diagonal v ∧
      (∀ i, star (v i) * v i = 1) ∧ (∀ i, ‖v i‖ = 1) := by
  have hVr : V * V.conjTranspose = 1 := mul_eq_one_comm.mp hV
  have hinter : pMatrix x * V = V * pMatrix y := by
    rw [hP]
    simp only [← Matrix.mul_assoc, hVr, Matrix.one_mul]
  have hoff (i j : Fin 3) (hij : i ≠ j) : V i j = 0 := by
    have he := congrArg (fun A : Square 3 => A i j) hinter
    simp only [pMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hdiff : (pCoordinates x i : ℂ) - (pCoordinates y j : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (fun h => p_intervals_separate x y hx hy i j hij
        (Complex.ofReal_injective h))
    -- The entrywise intertwining equation makes this scalar difference times V i j zero.
    apply (mul_eq_zero.mp (show ((pCoordinates x i : ℂ) -
        (pCoordinates y j : ℂ)) * V i j = 0 by
      rw [sub_mul, he]
      ring)).resolve_left hdiff
  let v : Fin 3 → ℂ := fun i => V i i
  have hd : V = Matrix.diagonal v := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [v]
    · simp [hij, hoff i j hij]
  have hu (i : Fin 3) : star (v i) * v i = 1 := by
    have he := congrArg (fun A : Square 3 => A i i) hV
    simpa only [hd, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq] using he
  have hn (i : Fin 3) : ‖v i‖ = 1 := by
    have he := congrArg norm (hu i)
    simp only [norm_mul, norm_star, norm_one] at he
    nlinarith [norm_nonneg (v i)]
  exact ⟨v, hd, hu, hn⟩

private theorem phase_eq_of_positive_edge (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (v w : ℂ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : star v * v = 1)
    (h : (b : ℂ) = star v * (a : ℂ) * w) : w = v := by
  have hab : b = a := by
    have he := congrArg norm h
    simpa only [norm_mul, norm_star, hv, hw, Complex.norm_of_nonneg ha.le,
      Complex.norm_of_nonneg hb.le, one_mul, mul_one] using he
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hphase : star v * w = 1 := by
    apply mul_left_cancel₀ haC
    calc
      (a : ℂ) * (star v * w) = star v * (a : ℂ) * w := by ring
      _ = (b : ℂ) := h.symm
      _ = (a : ℂ) * 1 := by rw [hab, mul_one]
  have hstar : star v ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hu
    exact zero_ne_one hu
  exact mul_left_cancel₀ hstar (hphase.trans hu.symm)

theorem parameter_slice_rigidity (x y : Parameters)
    (hx : x ∈ parameterBox) (hy : y ∈ parameterBox) (V : Square 3)
    (hV : V.conjTranspose * V = 1)
    (hP : pMatrix y = V.conjTranspose * pMatrix x * V)
    (hQ : qMatrix y = V.conjTranspose * qMatrix x * V) : x = y := by
  obtain ⟨v, hd, hu, hn⟩ := separated_unitary_diagonal x y hx hy V hV hP
  have hentry (i j : Fin 3) : qMatrix y i j = star (v i) * qMatrix x i j * v j := by
    rw [hQ, hd, diagonal_conjugacy_entry]
  have hxpos := parameter_box_bounds x hx
  have hypos := parameter_box_bounds y hy
  have hv1 : v 1 = v 0 := phase_eq_of_positive_edge (x 6) (y 6)
    hxpos.2.1 hypos.2.1 (v 0) (v 1) (hn 0) (hn 1) (hu 0)
    (by simpa [qMatrix] using hentry 0 1)
  have hv2 : v 2 = v 0 := phase_eq_of_positive_edge (x 7) (y 7)
    hxpos.2.2.1 hypos.2.2.1 (v 0) (v 2) (hn 0) (hn 2) (hu 0)
    (by simpa [qMatrix] using hentry 0 2)
  have hv (i : Fin 3) : v i = v 0 := by
    fin_cases i
    · rfl
    · exact hv1
    · exact hv2
  have hconj (A : Square 3) : V.conjTranspose * A * V = A := by
    rw [hd]
    ext i j
    rw [diagonal_conjugacy_entry, hv i, hv j]
    calc
      star (v 0) * A i j * v 0 = (star (v 0) * v 0) * A i j := by ring
      _ = A i j := by rw [hu 0, one_mul]
  have hp : pMatrix y = pMatrix x := hP.trans (hconj _)
  have hq : qMatrix y = qMatrix x := hQ.trans (hconj _)
  have hpcoords (i : Fin 3) : pCoordinates x i = pCoordinates y i := by
    have he := congrArg (fun A : Square 3 => (A i i).re) hp.symm
    simpa only [pMatrix, Matrix.diagonal_apply_eq, Complex.ofReal_re] using he
  have hqre (i j : Fin 3) : (qMatrix x i j).re = (qMatrix y i j).re :=
    congrArg (fun A : Square 3 => (A i j).re) hq.symm
  have hqim (i j : Fin 3) : (qMatrix x i j).im = (qMatrix y i j).im :=
    congrArg (fun A : Square 3 => (A i j).im) hq.symm
  ext i
  fin_cases i
  · exact hpcoords 0
  · exact hpcoords 1
  · exact hpcoords 2
  · simpa [qMatrix] using hqre 0 0
  · simpa [qMatrix] using hqre 1 1
  · simpa [qMatrix] using hqre 2 2
  · simpa [qMatrix] using hqre 0 1
  · simpa [qMatrix] using hqre 0 2
  · simpa [qMatrix] using hqre 1 2
  · simpa [qMatrix] using hqim 1 2

#print axioms parameter_slice_rigidity
#assert_trust kernel parameter_slice_rigidity

end
end NLA.SP15

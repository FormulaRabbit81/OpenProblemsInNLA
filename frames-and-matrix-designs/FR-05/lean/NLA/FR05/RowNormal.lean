/-
Finite-dimensional normal vectors for the row-to-span reduction.

For a square matrix, the rows other than one distinguished row span at most
one dimension fewer than the ambient space.  This supplies the unit normal
used after conditioning in the proof of Lemma 3.7.
-/
import NLA.FR05.LeastSingular
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

open scoped RealInnerProductSpace

/-- Reindex the rows other than `i` by `Fin n` using `Fin.succAbove`. -/
theorem otherRowSpan_eq_span_succAbove {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    otherRowSpan A i =
      Submodule.span ℝ (Set.range fun j : Fin n ↦
        WithLp.toLp 2 (A (i.succAbove j))) := by
  unfold otherRowSpan
  congr 1
  ext x
  constructor
  · rintro ⟨j, hji, hx⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
    refine ⟨k, ?_⟩
    subst j
    exact hx.symm
  · rintro ⟨j, hj⟩
    refine ⟨i.succAbove j, Fin.succAbove_ne i j, ?_⟩
    exact hj.symm

/-- The other-row span has dimension at most `n`. -/
theorem finrank_otherRowSpan_le {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    Module.finrank ℝ (otherRowSpan A i) ≤ n := by
  rw [otherRowSpan_eq_span_succAbove]
  change (Set.range (fun j : Fin n ↦
    WithLp.toLp 2 (A (i.succAbove j)))).finrank ℝ ≤ n
  simpa using (finrank_range_le_card (R := ℝ)
    (fun j : Fin n ↦ WithLp.toLp 2 (A (i.succAbove j))))

/-- There is always a nonzero normal to the span of the other rows of a
square real matrix. -/
theorem nontrivial_otherRowSpan_orthogonal {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    Nontrivial (otherRowSpan A i)ᗮ := by
  have hspan : Module.finrank ℝ (otherRowSpan A i) ≤ n :=
    finrank_otherRowSpan_le A i
  have hsum := (otherRowSpan A i).finrank_add_finrank_orthogonal
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by
    simp
  have hpos : 0 < Module.finrank ℝ (otherRowSpan A i)ᗮ := by
    omega
  exact Module.nontrivial_of_finrank_pos hpos

/-- A unit vector orthogonal to all rows other than the distinguished row.
This is the algebraic normal-vector ingredient of the conditioning step;
measurable selection remains a separate issue. -/
theorem exists_unit_mem_otherRowSpan_orthogonal {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    ∃ v : EuclideanSpace ℝ (Fin (n + 1)),
      v ∈ (otherRowSpan A i)ᗮ ∧ ‖v‖ = 1 := by
  let _ : Nontrivial (otherRowSpan A i)ᗮ := nontrivial_otherRowSpan_orthogonal A i
  obtain ⟨w, hw⟩ := exists_ne (0 : (otherRowSpan A i)ᗮ)
  let v : EuclideanSpace ℝ (Fin (n + 1)) :=
    (‖(w : EuclideanSpace ℝ (Fin (n + 1)))‖)⁻¹ • (w : EuclideanSpace ℝ (Fin (n + 1)))
  have hwcoe : (w : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    intro h
    apply hw
    exact Subtype.ext h
  have hwpos : 0 < ‖(w : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
    norm_pos_iff.mpr hwcoe
  refine ⟨v, ?_, ?_⟩
  · exact (otherRowSpan A i)ᗮ.smul_mem _ w.property
  · dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hwpos.le)]
    exact inv_mul_cancel₀ hwpos.ne'

end NLA.FR05

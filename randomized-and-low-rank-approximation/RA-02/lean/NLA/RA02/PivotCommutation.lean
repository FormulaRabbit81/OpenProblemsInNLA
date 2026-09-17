/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Two actual nonzero complex rank-one pivots commute. The scalar calculation
has fixed size; no matrix entries or dimensions are numerically enumerated.
-/
import NLA.RA02.PivotAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma two_pivot_entry (a d b c X u v y z : ℂ)
    (ha : a ≠ 0) (hd : d ≠ 0) (hda : d - c * b / a ≠ 0) :
    X - u * y / a - (v - u * b / a) * (z - c * y / a) / (d - c * b / a) =
      X - v * z / d - (u - v * c / d) * (y - b * z / d) / (a - b * c / d) := by
  have hmul : a * (d - c * b / a) = a * d - b * c := by
    field_simp [ha] <;> ring
  have hdet : a * d - b * c ≠ 0 := by
    rw [← hmul]
    exact mul_ne_zero ha hda
  have hfirst : d - c * b / a = (a * d - b * c) / a := by
    field_simp [ha] <;> ring
  have hsecond : a - b * c / d = (a * d - b * c) / d := by
    field_simp [hd] <;> ring
  rw [hfirst, hsecond]
  field_simp [ha, hd, hdet] <;> ring

lemma choleskyStep_commute {n : ℕ} (A : Square n) (i j : Fin n)
    (hi : A i i ≠ 0) (hj : A j j ≠ 0)
    (hij : choleskyStep A i j j ≠ 0) (hji : choleskyStep A j i i ≠ 0) :
    choleskyStep (choleskyStep A i) j = choleskyStep (choleskyStep A j) i := by
  have hij' : A j j - A j i * A i j / A i i ≠ 0 := by
    simpa only [choleskyStep, hi, ↓reduceIte] using hij
  have hji' : A i i - A i j * A j i / A j j ≠ 0 := by
    simpa only [choleskyStep, hj, ↓reduceIte] using hji
  ext x y
  simp only [choleskyStep, hi, hj, hij', hji', ↓reduceIte]
  exact two_pivot_entry (A i i) (A j j) (A i j) (A j i)
    (A x y) (A x i) (A x j) (A i y) (A j y) hi hj hij'

#print axioms two_pivot_entry
#assert_trust kernel two_pivot_entry
#print axioms choleskyStep_commute
#assert_trust kernel choleskyStep_commute

end
end NLA.RA02

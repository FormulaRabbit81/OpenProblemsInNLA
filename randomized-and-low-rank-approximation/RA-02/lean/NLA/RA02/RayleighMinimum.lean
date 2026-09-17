/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The least genuinely ordered eigenvalue is bounded by the actual complex
Rayleigh quotient. The lower-bound argument works for all Hermitian matrices.
-/
import NLA.RA02.OrderedSpectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma rayleigh_range_bddBelow {n : ℕ} (A : Square n) :
    BddBelow (Set.range (fun v : {v : EuclideanSpace ℂ (Fin n) // v ≠ 0} =>
      (inner ℂ (Matrix.toEuclideanLin A (v : EuclideanSpace ℂ (Fin n)))
        (v : EuclideanSpace ℂ (Fin n))).re / ‖(v : EuclideanSpace ℂ (Fin n))‖ ^ 2)) := by
  let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  refine ⟨-‖T‖, ?_⟩
  rintro y ⟨v, rfl⟩
  have h := (abs_le.mp (T.rayleighQuotient_le_norm (v : EuclideanSpace ℂ (Fin n)))).1
  change -‖T‖ ≤
    (inner ℂ (Matrix.toEuclideanLin A (v : EuclideanSpace ℂ (Fin n)))
      (v : EuclideanSpace ℂ (Fin n))).re / ‖(v : EuclideanSpace ℂ (Fin n))‖ ^ 2 at h
  exact h

lemma last_ordered_le_rayleigh_iInf (m : ℕ) (A : Square (m + 1))
    (hA : A.IsHermitian) :
    orderedEigenvalues A hA (Fin.last m) ≤
      ⨅ v : {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0},
        (inner ℂ (Matrix.toEuclideanLin A (v : EuclideanSpace ℂ (Fin (m + 1))))
          (v : EuclideanSpace ℂ (Fin (m + 1)))).re /
            ‖(v : EuclideanSpace ℂ (Fin (m + 1)))‖ ^ 2 := by
  let L := Matrix.toEuclideanLin A
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let μ : ℝ := ⨅ v : {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0},
    (inner ℂ (L (v : EuclideanSpace ℂ (Fin (m + 1))))
      (v : EuclideanSpace ℂ (Fin (m + 1)))).re / ‖(v : EuclideanSpace ℂ (Fin (m + 1)))‖ ^ 2
  have hμ : Module.End.HasEigenvalue L (μ : ℂ) :=
    hL.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨i, hi⟩ := hL.exists_eigenvalues_eq finrank_euclideanSpace hμ
  have hreal : hA.eigenvalues₀ i = μ := by
    apply Complex.ofReal_inj.mp
    exact hi
  have hiLast : i ≤ Fin.cast (Fintype.card_fin (m + 1)).symm (Fin.last m) := by
    change i.val ≤ m
    have hiLt : i.val < m + 1 := by
      simpa only [Fintype.card_fin] using i.isLt
    exact Nat.le_of_lt_succ hiLt
  have hbound := hA.eigenvalues₀_antitone hiLast
  change orderedEigenvalues A hA (Fin.last m) ≤ hA.eigenvalues₀ i at hbound
  rw [hreal] at hbound
  exact hbound

theorem least_eigenvalue_rayleigh (m : ℕ) (A : Square (m + 1))
    (hA : A.IsHermitian) (x : Fin (m + 1) → ℂ) (hx : x ≠ 0) :
    orderedEigenvalues A hA (Fin.last m) ≤ quadraticValue A x / squaredNorm x := by
  let v : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 x
  have hv : v ≠ 0 := euclidean_toLp_ne_zero x hx
  have hInf := ciInf_le (rayleigh_range_bddBelow A)
    (⟨v, hv⟩ : {v : EuclideanSpace ℂ (Fin (m + 1)) // v ≠ 0})
  have h := (last_ordered_le_rayleigh_iInf m A hA).trans hInf
  simpa only [v, euclidean_quadratic, euclidean_norm_sq] using h

#print axioms least_eigenvalue_rayleigh
#assert_trust kernel least_eigenvalue_rayleigh

end
end NLA.RA02

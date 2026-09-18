/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The frozen triangular predicate agrees with Mathlib's existing predicate.
Its multiplication theorem handles closure; diagonal multiplicativity then
follows by removing exactly the vanishing complementary-fiber summands.
-/
import NLA.MF06.BlockCoordinates
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma isUpperBlockTriangular_iff {d r : ℕ} (b : Fin d → Fin r) (A : Square d) :
    IsUpperBlockTriangular b A ↔ A.BlockTriangular b := by
  constructor
  · intro h i j hij
    exact h i j hij
  · intro h i j hij
    exact h hij

lemma upperBlock_one {d r : ℕ} (b : Fin d → Fin r) :
    IsUpperBlockTriangular b (1 : Square d) :=
  (isUpperBlockTriangular_iff b 1).mpr Matrix.blockTriangular_one

lemma upperBlock_mul {d r : ℕ} (b : Fin d → Fin r) (A B : Square d)
    (hA : IsUpperBlockTriangular b A) (hB : IsUpperBlockTriangular b B) :
    IsUpperBlockTriangular b (A * B) :=
  (isUpperBlockTriangular_iff b (A * B)).mpr
    (((isUpperBlockTriangular_iff b A).mp hA).mul
      ((isUpperBlockTriangular_iff b B).mp hB))

lemma blockMatrix_one {d r : ℕ} (b : Fin d → Fin r) (i : Fin r) :
    blockMatrix b i (1 : Square d) = 1 :=
  Matrix.submatrix_one (blockCoordinate b i) (blockCoordinate_injective b i)

lemma blockMatrix_mul {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (A B : Square d) (hA : IsUpperBlockTriangular b A)
    (hB : IsUpperBlockTriangular b B) :
    blockMatrix b i (A * B) = blockMatrix b i A * blockMatrix b i B := by
  ext u v
  change (∑ j : Fin d, A (blockCoordinate b i u) j * B j (blockCoordinate b i v)) =
    ∑ j : Fin (blockDim b i),
      A (blockCoordinate b i u) (blockCoordinate b i j) *
        B (blockCoordinate b i j) (blockCoordinate b i v)
  apply blockCoordinate_sum b i
  intro j hj
  rcases lt_or_gt_of_ne hj with hji | hij
  · have hz := hA (blockCoordinate b i u) j (by
      simpa only [blockCoordinate_label] using hji)
    rw [hz, zero_mul]
  · have hz := hB j (blockCoordinate b i v) (by
      simpa only [blockCoordinate_label] using hij)
    rw [hz, mul_zero]

lemma matrixProduct_upperBlock {d r : ℕ} (b : Fin d → Fin r)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    IsUpperBlockTriangular b (matrixProduct w) := by
  induction w with
  | nil => simpa only [matrixProduct_nil] using upperBlock_one b
  | cons A w ih =>
      obtain ⟨hA, hw⟩ := (WordIn_cons_iff M A w).mp hw
      rw [matrixProduct_cons]
      exact upperBlock_mul b (matrixProduct w) A (ih hw) (hupper A hA)

/-- The same original word supplies every diagonal block at every time. -/
lemma blockMatrix_matrixProduct {d r : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (M : Set (Square d)) (hupper : ∀ A ∈ M, IsUpperBlockTriangular b A)
    (w : List (Square d)) (hw : WordIn M w) :
    blockMatrix b i (matrixProduct w) = matrixProduct (w.map (blockMatrix b i)) := by
  induction w with
  | nil => simp only [List.map_nil, matrixProduct_nil, blockMatrix_one]
  | cons A w ih =>
      obtain ⟨hA, hw⟩ := (WordIn_cons_iff M A w).mp hw
      rw [List.map_cons, matrixProduct_cons, matrixProduct_cons,
        blockMatrix_mul b i (matrixProduct w) A
          (matrixProduct_upperBlock b M hupper w hw) (hupper A hA), ih hw]

#print axioms blockMatrix_matrixProduct
#assert_trust kernel blockMatrix_matrixProduct

end NLA.MF06

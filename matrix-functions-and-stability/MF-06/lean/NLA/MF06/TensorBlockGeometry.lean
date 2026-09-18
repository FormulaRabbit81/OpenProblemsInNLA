/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A tensor block is indexed by the original block of its first factor. The
coordinate map below proves the actual compressed tensor is a submatrix of
the tensor of that original diagonal block and the full second factor.
-/
import NLA.MF06.FiberCompression
import NLA.MF06.BlockAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

def tensorBlockLabel {d r : ℕ} (b : Fin d → Fin r) (n : ℕ) (u : Fin (d * n)) : Fin r :=
  b ((finProdFinEquiv (m := d) (n := n)).symm u).1

lemma tensorBlockLabel_surjective {d r n : ℕ} (b : Fin d → Fin r)
    (hb : Function.Surjective b) (hn : 1 ≤ n) : Function.Surjective (tensorBlockLabel b n) := by
  intro i
  obtain ⟨j, hj⟩ := hb i
  refine ⟨finProdFinEquiv (j, (⟨0, hn⟩ : Fin n)), ?_⟩
  simpa only [tensorBlockLabel, Equiv.symm_apply_apply] using hj

lemma tensorBlock_upper {d r n : ℕ} (b : Fin d → Fin r) (A : Square d) (B : Square n)
    (hA : IsUpperBlockTriangular b A) : IsUpperBlockTriangular (tensorBlockLabel b n) (tensorMatrix A B) := by
  intro u v huv
  change A ((finProdFinEquiv (m := d) (n := n)).symm u).1
      ((finProdFinEquiv (m := d) (n := n)).symm v).1 *
    B ((finProdFinEquiv (m := d) (n := n)).symm u).2
      ((finProdFinEquiv (m := d) (n := n)).symm v).2 = 0
  rw [hA _ _ huv, zero_mul]

def tensorFirstCoordinate {d r : ℕ} (b : Fin d → Fin r) (n : ℕ) (i : Fin r)
    (u : Fin (blockDim (tensorBlockLabel b n) i)) : Fin d :=
  ((finProdFinEquiv (m := d) (n := n)).symm (blockCoordinate (tensorBlockLabel b n) i u)).1

lemma tensorFirstCoordinate_label {d r : ℕ} (b : Fin d → Fin r) (n : ℕ) (i : Fin r)
    (u : Fin (blockDim (tensorBlockLabel b n) i)) : b (tensorFirstCoordinate b n i u) = i :=
  blockCoordinate_label (tensorBlockLabel b n) i u

def tensorBlockCoordinate {d r : ℕ} (b : Fin d → Fin r) (n : ℕ) (i : Fin r)
    (u : Fin (blockDim (tensorBlockLabel b n) i)) : Fin (blockDim b i * n) :=
  finProdFinEquiv (fiberCoordinate b i (tensorFirstCoordinate b n i)
    (tensorFirstCoordinate_label b n i) u,
      ((finProdFinEquiv (m := d) (n := n)).symm (blockCoordinate (tensorBlockLabel b n) i u)).2)

lemma tensorBlock_submatrix {d r n : ℕ} (b : Fin d → Fin r) (i : Fin r)
    (A : Square d) (B : Square n) :
    blockMatrix (tensorBlockLabel b n) i (tensorMatrix A B) =
      (tensorMatrix (blockMatrix b i A) B).submatrix
        (tensorBlockCoordinate b n i) (tensorBlockCoordinate b n i) := by
  ext u v
  simp only [blockMatrix, tensorMatrix, Matrix.kronecker, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, tensorBlockCoordinate, Equiv.symm_apply_apply,
    blockCoordinate_fiberCoordinate, tensorFirstCoordinate]

#print axioms tensorBlock_upper
#assert_trust kernel tensorBlock_upper
#print axioms tensorBlock_submatrix
#assert_trust kernel tensorBlock_submatrix

end NLA.MF06

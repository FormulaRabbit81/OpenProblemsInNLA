/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The adapted basis produces actual two-sided inverse coordinate matrices.
Preservation of each original prefix subspace makes the conjugated matrices
upper block triangular in the exact frozen label convention.
-/
import NLA.MF06.FlagLabeling

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

def ambientBasis (d : ℕ) : Module.Basis (Fin d) ℂ (EuclideanVector d) :=
  (EuclideanSpace.basisFun (Fin d) ℂ).toBasis

def basisForward {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) : Square d :=
  LinearMap.toMatrix B (ambientBasis d) LinearMap.id

def basisBackward {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) : Square d :=
  LinearMap.toMatrix (ambientBasis d) B LinearMap.id

def inBasis {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (A : Square d) : Square d :=
  LinearMap.toMatrix B B (Matrix.toEuclideanLin A)

lemma basisForward_mul_backward {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) :
    basisForward B * basisBackward B = 1 := by
  unfold basisForward basisBackward
  rw [← LinearMap.toMatrix_comp (ambientBasis d) B (ambientBasis d)]
  simp only [LinearMap.id_comp, LinearMap.toMatrix_id]

lemma basisBackward_mul_forward {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) :
    basisBackward B * basisForward B = 1 := by
  unfold basisForward basisBackward
  rw [← LinearMap.toMatrix_comp B (ambientBasis d) B]
  simp only [LinearMap.id_comp, LinearMap.toMatrix_id]

lemma ambient_matrix_semantics {d : ℕ} (A : Square d) :
    LinearMap.toMatrix (ambientBasis d) (ambientBasis d) (Matrix.toEuclideanLin A) = A := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearMap.toMatrix_toLin _ _ A

lemma inBasis_eq_conjugate {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d))
    (A : Square d) : inBasis B A = basisBackward B * A * basisForward B := by
  symm
  calc
    basisBackward B * A * basisForward B =
        basisBackward B * LinearMap.toMatrix (ambientBasis d) (ambientBasis d)
          (Matrix.toEuclideanLin A) * basisForward B := by rw [ambient_matrix_semantics]
    _ = inBasis B A := by
      unfold basisBackward basisForward inBasis
      rw [← LinearMap.toMatrix_comp (ambientBasis d) (ambientBasis d) B,
        ← LinearMap.toMatrix_comp B (ambientBasis d) B]
      simp only [LinearMap.id_comp, LinearMap.comp_id]

lemma inBasis_entry {d : ℕ} (B : Module.Basis (Fin d) ℂ (EuclideanVector d))
    (A : Square d) (i j : Fin d) : inBasis B A i j = B.repr (applyMatrix A (B j)) i := by
  rw [inBasis, LinearMap.toMatrix_apply]
  rfl

lemma inBasis_upper_of_flag {d r : ℕ}
    (F : Fin (r + 1) → Submodule ℂ (EuclideanVector d))
    (B : Module.Basis (Fin d) ℂ (EuclideanVector d)) (b : Fin d → Fin r)
    (hmem : ∀ j i, B j ∈ F i ↔ (b j).val < i.val)
    (hspan : ∀ i, Submodule.span ℂ (B '' {j | (b j).val < i.val}) = F i)
    (M : Set (Square d)) (hinv : ∀ i, FamilyInvariant M (F i)) :
    ∀ A ∈ M, IsUpperBlockTriangular b (inBasis B A) := by
  intro A hA i j hij
  rw [inBasis_entry]
  have hj : B j ∈ F (b j).succ := (hmem j _).mpr (Nat.lt_succ_self _)
  have hAj : applyMatrix A (B j) ∈ F (b j).succ := hinv _ A hA (B j) hj
  rw [← hspan (b j).succ] at hAj
  apply Finsupp.notMem_support_iff.mp
  intro hi
  have hi' := B.repr_support_subset_of_mem_span _ hAj hi
  change (b i).val < (b j).val + 1 at hi'
  have hlt : (b j).val < (b i).val := hij
  omega

#print axioms basisForward_mul_backward
#assert_trust kernel basisForward_mul_backward
#print axioms inBasis_eq_conjugate
#assert_trust kernel inBasis_eq_conjugate
#print axioms inBasis_upper_of_flag
#assert_trust kernel inBasis_upper_of_flag

end NLA.MF06

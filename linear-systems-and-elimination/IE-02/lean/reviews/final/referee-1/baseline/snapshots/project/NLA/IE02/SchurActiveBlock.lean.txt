/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's Euclidean coordinate norm, finite tuple, polynomial divX,
and continuous operator-norm APIs.

The input loses its last coordinate, while the output gains a first zero.
Both operator-norm inequalities include a zero-dimensional active block.
-/
import NLA.IE02.Definitions
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.BigOperators.Fin
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section
open scoped BigOperators

theorem appendVector_norm_sq {n : ℕ} (g : H n) (η : ℂ) :
    ‖appendVector g η‖ ^ 2 = ‖g‖ ^ 2 + ‖η‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc,
    appendVector, Fin.snoc_castSucc, Fin.snoc_last]

theorem prependZero_norm {n : ℕ} (g : H n) : ‖prependZero g‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, prependZero, Fin.sum_univ_succ]

theorem appendVector_norm_zero {n : ℕ} (g : H n) : ‖appendVector g 0‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [appendVector_norm_sq]

theorem norm_le_appendVector {n : ℕ} (g : H n) (η : ℂ) : ‖g‖ ≤ ‖appendVector g η‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [appendVector_norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem exists_appendVector {n : ℕ} (x : H (n + 1)) :
    ∃ (g : H n) (η : ℂ), x = appendVector g η := by
  refine ⟨WithLp.toLp 2 (fun i => x i.castSucc), x (Fin.last n), ?_⟩
  apply PiLp.ext
  intro i
  -- Expose the frozen Euclidean tuple wrappers as the original snoc decomposition.
  change x i = Fin.snoc (α := fun _ : Fin (n + 1) => ℂ)
    (fun j : Fin n => x j.castSucc) (x (Fin.last n)) i
  exact (congrFun (Fin.snoc_init_self (α := fun _ : Fin (n + 1) => ℂ)
    (q := fun j : Fin (n + 1) => x j)) i).symm

/-- The zero constant coefficient identifies the active block once for both Schur uses. -/
theorem activeBlock_toeplitz_divX (n : ℕ) (q : Poly) (hq : q.coeff 0 = 0) :
    activeBlock (toeplitz (n + 1) q) = toeplitz n q.divX := by
  ext i j
  simp only [activeBlock, toeplitz, Fin.val_succ, Fin.val_castSucc,
    Polynomial.coeff_divX]
  by_cases hji : j.val ≤ i.val
  · have hji' : j.val ≤ i.val + 1 := by omega
    rw [if_pos hji', if_pos hji]
    congr 1
    omega
  · rw [if_neg hji]
    by_cases hji' : j.val ≤ i.val + 1
    · rw [if_pos hji']
      have heq : i.val + 1 - j.val = 0 := by omega
      rw [heq, hq]
    · rw [if_neg hji']

theorem schur_active_block {n : ℕ} (Z : Square (n + 1)) (hZ : IsToeplitz Z)
    (hdiag : ∀ i, Z i i = 0) (hcon : operatorNorm Z ≤ 1) :
    IsToeplitz (activeBlock Z) ∧ operatorNorm Z = operatorNorm (activeBlock Z) ∧
    ∀ (g : H n) (η : ℂ),
      euclideanLin Z (appendVector g η) = prependZero (euclideanLin (activeBlock Z) g) ∧
      ‖appendVector g η‖ ^ 2 = ‖g‖ ^ 2 + ‖η‖ ^ 2 ∧
      (‖euclideanLin Z (appendVector g η)‖ = ‖appendVector g η‖ ↔
        η = 0 ∧ ‖euclideanLin (activeBlock Z) g‖ = ‖g‖) := by
  rcases hZ with ⟨p, rfl⟩
  let V : Square n := activeBlock (toeplitz (n + 1) p)
  have hp0 : p.coeff 0 = 0 := by
    simpa [toeplitz] using hdiag (0 : Fin (n + 1))
  have hblock : V = toeplitz n p.divX := activeBlock_toeplitz_divX n p hp0
  have hrow (j : Fin (n + 1)) : toeplitz (n + 1) p 0 j = 0 := by
    simp [toeplitz, hp0]
  have hlast (i : Fin (n + 1)) : toeplitz (n + 1) p i (Fin.last n) = 0 := by
    by_cases hi : n ≤ i.val
    · have heq : i.val = n := by omega
      simp [toeplitz, heq, hp0]
    · simp [toeplitz, hi]
  have haction (g : H n) (η : ℂ) :
      euclideanLin (toeplitz (n + 1) p) (appendVector g η) =
        prependZero (euclideanLin V g) := by
    apply PiLp.ext
    intro i
    cases i using Fin.cases with
    | zero =>
      -- Expose the first coordinate of matrix action; the first row is zero.
      change (∑ j : Fin (n + 1), toeplitz (n + 1) p 0 j * (appendVector g η) j) = 0
      simp only [hrow, zero_mul, Finset.sum_const_zero]
    | succ i =>
      -- Expose a successor output coordinate and the exact active-block row.
      change (∑ j : Fin (n + 1), toeplitz (n + 1) p i.succ j * (appendVector g η) j) =
        ∑ j : Fin n, V i j * g j
      rw [Fin.sum_univ_castSucc]
      simp only [hlast, zero_mul, add_zero, appendVector, PiLp.toLp_apply,
        Fin.snoc_castSucc, V, activeBlock]
  have hle : operatorNorm V ≤ operatorNorm (toeplitz (n + 1) p) := by
    apply ContinuousLinearMap.opNorm_le_bound (euclideanCLM V)
      (norm_nonneg (euclideanCLM (toeplitz (n + 1) p)))
    intro g
    calc
      ‖euclideanLin V g‖ = ‖prependZero (euclideanLin V g)‖ := (prependZero_norm _).symm
      _ = ‖euclideanLin (toeplitz (n + 1) p) (appendVector g 0)‖ :=
        congrArg norm (haction g 0).symm
      _ ≤ operatorNorm (toeplitz (n + 1) p) * ‖appendVector g 0‖ :=
        (euclideanCLM (toeplitz (n + 1) p)).le_opNorm _
      _ = operatorNorm (toeplitz (n + 1) p) * ‖g‖ := by rw [appendVector_norm_zero]
  have hge : operatorNorm (toeplitz (n + 1) p) ≤ operatorNorm V := by
    apply ContinuousLinearMap.opNorm_le_bound (euclideanCLM (toeplitz (n + 1) p))
      (norm_nonneg (euclideanCLM V))
    intro x
    obtain ⟨g, η, rfl⟩ := exists_appendVector x
    calc
      ‖euclideanLin (toeplitz (n + 1) p) (appendVector g η)‖ = ‖euclideanLin V g‖ := by
        rw [haction, prependZero_norm]
      _ ≤ operatorNorm V * ‖g‖ := (euclideanCLM V).le_opNorm g
      _ ≤ operatorNorm V * ‖appendVector g η‖ :=
        mul_le_mul_of_nonneg_left (norm_le_appendVector g η) (norm_nonneg (euclideanCLM V))
  have hnorm : operatorNorm (toeplitz (n + 1) p) = operatorNorm V := le_antisymm hge hle
  have hvcon : operatorNorm V ≤ 1 := hle.trans hcon
  refine ⟨⟨p.divX, hblock⟩, hnorm, ?_⟩
  intro g η
  refine ⟨haction g η, appendVector_norm_sq g η, ?_⟩
  constructor
  · intro heq
    rw [haction, prependZero_norm] at heq
    have hvg : ‖euclideanLin V g‖ ≤ ‖g‖ := by
      calc
        ‖euclideanLin V g‖ ≤ operatorNorm V * ‖g‖ := (euclideanCLM V).le_opNorm g
        _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hvcon (norm_nonneg g)
        _ = ‖g‖ := one_mul _
    have hsquared : ‖euclideanLin V g‖ ^ 2 = ‖g‖ ^ 2 + ‖η‖ ^ 2 := by
      rw [heq, appendVector_norm_sq]
    have hsqle := (sq_le_sq₀ (norm_nonneg (euclideanLin V g)) (norm_nonneg g)).mpr hvg
    have hηsq : ‖η‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖η‖]
    have hη : η = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hηsq)
    refine ⟨hη, ?_⟩
    rw [hη, appendVector_norm_zero] at heq
    exact heq
  · rintro ⟨rfl, hg⟩
    rw [haction, prependZero_norm, appendVector_norm_zero]
    exact hg

#print axioms schur_active_block
#assert_trust kernel schur_active_block

end
end NLA.IE02

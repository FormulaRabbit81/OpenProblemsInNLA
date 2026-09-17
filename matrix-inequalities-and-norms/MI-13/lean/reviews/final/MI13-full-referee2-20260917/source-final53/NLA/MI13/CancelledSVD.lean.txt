/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Nobori's original question, Audenaert's
refined commutator theorem, and the repository reduction retain their attribution.

The canceled first entry removes the only coefficient requiring twice the
largest singular value squared. Every other entry uses the first two actual
singular values; unitary Frobenius invariance gives the final factor two.
-/
import NLA.MI13.ElementaryBounds
import NLA.MI13.UnitaryInvariance
import NLA.MI13.CommutatorEigenspaces

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section
open scoped BigOperators Matrix

/-- The total first-entry operation is linear, including its zero-dimensional branch. -/
def firstEntryLinear (r : ℕ) : Square r →ₗ[ℂ] ℂ where
  toFun := firstEntry
  map_add' A B := by
    by_cases h : 0 < r <;> simp [firstEntry, h]
  map_smul' z A := by
    by_cases h : 0 < r <;> simp [firstEntry, h]

theorem svd_corner_functional {r : ℕ} (X U V : Square r) :
    ∃ f : Square r →ₗ[ℂ] ℂ,
      ∀ Z : Square r, f Z = firstEntry (U.conjTranspose * commutator X Z * V) := by
  refine ⟨(firstEntryLinear r).comp
    ((LinearMap.mulLeftRight ℂ (U.conjTranspose, V)).comp (commutatorLinear X)), ?_⟩
  intro Z
  -- The three bundled maps have exactly the displayed entry, left/right
  -- multiplication, and commutator functions as their defining operations.
  rfl

theorem svd_commutator_transform {r : ℕ} (X Z U V : Square r)
    (hU : IsUnitary U) (hV : IsUnitary V)
    (hsvd : X = U * singularDiagonal X * V.conjTranspose) :
    U.conjTranspose * commutator X Z * V =
      singularDiagonal X * (V.conjTranspose * Z * V) -
        (U.conjTranspose * Z * U) * singularDiagonal X := by
  calc
    U.conjTranspose * commutator X Z * V =
        U.conjTranspose * commutator (U * singularDiagonal X * V.conjTranspose) Z * V :=
      congrArg (fun A : Square r => U.conjTranspose * commutator A Z * V) hsvd
    _ = (U.conjTranspose * U) * singularDiagonal X * (V.conjTranspose * Z * V) -
        (U.conjTranspose * Z * U) * singularDiagonal X * (V.conjTranspose * V) := by
      simp only [commutator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = singularDiagonal X * (V.conjTranspose * Z * V) -
        (U.conjTranspose * Z * U) * singularDiagonal X := by
      rw [hU.1, hV.1, Matrix.one_mul, Matrix.mul_one]

theorem svd_diagonal_entry {r : ℕ} (X P Q : Square r) (i j : Fin r) :
    (singularDiagonal X * P - Q * singularDiagonal X) i j =
      (singularValue X i.val : ℂ) * P i j - (singularValue X j.val : ℂ) * Q i j := by
  simp only [singularDiagonal, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, mul_comm]

theorem cancelled_svd_entry_bound {r : ℕ} (hr : 0 < r) (X P Q : Square r)
    (hcorner : firstEntry (singularDiagonal X * P - Q * singularDiagonal X) = 0)
    (i j : Fin r) :
    ‖(singularDiagonal X * P - Q * singularDiagonal X) i j‖ ^ 2 ≤
      (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) * (‖P i j‖ ^ 2 + ‖Q i j‖ ^ 2) := by
  by_cases hij : (i.val, j.val) = (0, 0)
  · have hi : i = (⟨0, hr⟩ : Fin r) := Fin.ext (congrArg Prod.fst hij)
    have hj : j = (⟨0, hr⟩ : Fin r) := Fin.ext (congrArg Prod.snd hij)
    -- Unfold only the total first-entry selector. Positivity chooses its
    -- genuine matrix-entry branch; Fin proof fields agree by proof irrelevance.
    have h00 : (singularDiagonal X * P - Q * singularDiagonal X)
        ⟨0, hr⟩ ⟨0, hr⟩ = 0 := by
      simpa only [firstEntry, dif_pos hr] using hcorner
    have hzero : (singularDiagonal X * P - Q * singularDiagonal X) i j = 0 := by
      simpa only [hi, hj] using h00
    rw [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · have hs := singular_values_semantics X
    rw [svd_diagonal_entry]
    calc
      ‖(singularValue X i.val : ℂ) * P i j - (singularValue X j.val : ℂ) * Q i j‖ ^ 2 ≤
          (singularValue X i.val ^ 2 + singularValue X j.val ^ 2) *
            (‖P i j‖ ^ 2 + ‖Q i j‖ ^ 2) :=
        two_coordinate_bound _ _ (hs.1 i.val) (hs.1 j.val) (P i j) (Q i j)
      _ ≤ (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) *
          (‖P i j‖ ^ 2 + ‖Q i j‖ ^ 2) :=
        mul_le_mul_of_nonneg_right
          (off_corner_coefficient_bound (singularValue X) hs.1 hs.2.1 i.val j.val hij)
          (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem cancelled_svd_diagonal_bound {r : ℕ} (hr : 0 < r) (X P Q : Square r)
    (hcorner : firstEntry (singularDiagonal X * P - Q * singularDiagonal X) = 0) :
    frobeniusNorm (singularDiagonal X * P - Q * singularDiagonal X) ^ 2 ≤
      (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) *
        (frobeniusNorm P ^ 2 + frobeniusNorm Q ^ 2) := by
  have hsum : (∑ i : Fin r, ∑ j : Fin r,
      ‖(singularDiagonal X * P - Q * singularDiagonal X) i j‖ ^ 2) ≤
      ∑ i : Fin r, ∑ j : Fin r, (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) *
        (‖P i j‖ ^ 2 + ‖Q i j‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact cancelled_svd_entry_bound hr X P Q hcorner i j
  -- Convert the actual Euclidean Frobenius squares to the full entry sums.
  -- Distributing finite sums retains every nonnegative term, including (0,0).
  simpa only [frobenius_norm_sq_eq_entries, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add] using hsum

theorem cancelled_svd_bound {r : ℕ} (hr : 2 ≤ r) (X Z U V : Square r)
    (hU : IsUnitary U) (hV : IsUnitary V)
    (hsvd : X = U * singularDiagonal X * V.conjTranspose)
    (hcorner : firstEntry (U.conjTranspose * commutator X Z * V) = 0) :
    frobeniusNorm (commutator X Z) ^ 2 ≤
      2 * (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) * frobeniusNorm Z ^ 2 := by
  have hUt : IsUnitary U.conjTranspose := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hU.2 hU.1
  have hVt : IsUnitary V.conjTranspose := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hV.2 hV.1
  let P : Square r := V.conjTranspose * Z * V
  let Q : Square r := U.conjTranspose * Z * U
  have htransform : U.conjTranspose * commutator X Z * V =
      singularDiagonal X * P - Q * singularDiagonal X :=
    svd_commutator_transform X Z U V hU hV hsvd
  have hcorner' : firstEntry (singularDiagonal X * P - Q * singularDiagonal X) = 0 := by
    rw [← htransform]
    exact hcorner
  have hbound := cancelled_svd_diagonal_bound (by omega : 0 < r) X P Q hcorner'
  have hcomm := (unitary_norm_invariance (commutator X Z) U.conjTranspose V hUt hV).1
  have hP : frobeniusNorm P = frobeniusNorm Z :=
    (unitary_norm_invariance Z V.conjTranspose V hVt hV).1
  have hQ : frobeniusNorm Q = frobeniusNorm Z :=
    (unitary_norm_invariance Z U.conjTranspose U hUt hU).1
  calc
    frobeniusNorm (commutator X Z) ^ 2 =
        frobeniusNorm (singularDiagonal X * P - Q * singularDiagonal X) ^ 2 := by
      rw [← htransform, hcomm]
    _ ≤ (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) *
        (frobeniusNorm P ^ 2 + frobeniusNorm Q ^ 2) := hbound
    _ = 2 * (singularValue X 0 ^ 2 + singularValue X 1 ^ 2) * frobeniusNorm Z ^ 2 := by
      rw [hP, hQ]
      ring

#print axioms svd_corner_functional
#assert_trust kernel svd_corner_functional
#print axioms cancelled_svd_bound
#assert_trust kernel cancelled_svd_bound

end
end NLA.MI13

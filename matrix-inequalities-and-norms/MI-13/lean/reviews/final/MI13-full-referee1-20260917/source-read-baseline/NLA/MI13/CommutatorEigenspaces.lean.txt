/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; prior mathematical attribution is retained.

Positive commutator eigenspaces have two orthogonal nonzero vectors. Consequently
every complex linear functional has a nonzero kernel vector in that eigenspace.
-/
import NLA.MI13.CommutatorAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section

def commutatorLinear {r : ℕ} (X : Square r) : Square r →ₗ[ℂ] Square r where
  toFun := commutator X
  map_add' Y Z := by simp only [commutator, mul_add, add_mul]; abel
  map_smul' z Y := by
    simp only [commutator, mul_smul_comm, smul_mul_assoc, smul_sub, RingHom.id_apply]

def commutatorTLinear {r : ℕ} (X : Square r) : Square r →ₗ[ℂ] Square r :=
  (commutatorLinear X.conjTranspose).comp (commutatorLinear X)

@[simp] theorem commutatorTLinear_apply {r : ℕ} (X Y : Square r) :
    commutatorTLinear X Y = commutatorT X Y := rfl

@[simp] theorem commutatorJ_smul {r : ℕ} (X Y : Square r) (z : ℂ) :
    commutatorJ X (z • Y) = star z • commutatorJ X Y := by
  simp only [commutatorJ, commutator, Matrix.conjTranspose_smul,
    mul_smul_comm, smul_mul_assoc, smul_sub]

theorem hsInner_self {r : ℕ} (Y : Square r) :
    hsInner Y Y = ((frobeniusNorm Y ^ 2 : ℝ) : ℂ) := by
  simp only [hsInner, inner_self_eq_norm_sq_to_K, frobeniusNorm,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]

theorem positive_eigenvector_pair {r : ℕ} (X Y : Square r) (lam : ℝ)
    (hlam : 0 < lam) (hY : Y ≠ 0) (heig : commutatorT X Y = (lam : ℂ) • Y) :
    commutatorJ X Y ≠ 0 ∧
    commutatorT X (commutatorJ X Y) = (lam : ℂ) • commutatorJ X Y ∧
    hsInner Y (commutatorJ X Y) = 0 ∧
    frobeniusNorm (commutatorJ X Y) ^ 2 = lam * frobeniusNorm Y ^ 2 := by
  have hsym := commutator_conjugate_symmetry X Y (0 : Square r) (0 : ℂ)
  have henergy : frobeniusNorm (commutator X Y) ^ 2 = lam * frobeniusNorm Y ^ 2 := by
    have h := (commutator_adjoint X Y (0 : Square r)).2.2
    rw [heig, hsInner, flatten_smul, inner_smul_right] at h
    have hs := hsInner_self Y
    simp only [hsInner] at hs
    rw [hs] at h
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_mul] using h.symm)
  have hnorm : frobeniusNorm (commutatorJ X Y) ^ 2 = lam * frobeniusNorm Y ^ 2 := by
    rw [hsym.2.2.2.2]
    exact henergy
  have hypos : 0 < frobeniusNorm Y :=
    lt_of_le_of_ne (frobenius_semantics Y).2.2.1
      (Ne.symm (fun h => hY ((frobenius_semantics Y).2.2.2.mp h)))
  refine ⟨?_, ?_, hsym.2.2.2.1, hnorm⟩
  · intro hzero
    rw [hzero] at hnorm
    have hz : frobeniusNorm (0 : Square r) = 0 := (frobenius_semantics 0).2.2.2.mpr rfl
    rw [hz] at hnorm
    nlinarith [sq_pos_of_pos hypos]
  · rw [hsym.2.2.1, heig, commutatorJ_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]

theorem eigenspace_functional_kernel {r : ℕ} (X Y : Square r) (lam : ℝ)
    (hlam : 0 < lam) (hY : Y ≠ 0) (heig : commutatorT X Y = (lam : ℂ) • Y)
    (f : Square r →ₗ[ℂ] ℂ) :
    ∃ Z : Square r, Z ≠ 0 ∧ commutatorT X Z = (lam : ℂ) • Z ∧ f Z = 0 := by
  obtain ⟨hJ, heigJ, horth, hnormJ⟩ := positive_eigenvector_pair X Y lam hlam hY heig
  by_cases hfY : f Y = 0
  · exact ⟨Y, hY, heig, hfY⟩
  let Z : Square r := f Y • commutatorJ X Y - f (commutatorJ X Y) • Y
  have hZ : Z ≠ 0 := by
    intro hz
    have hinner := congrArg (fun W : Square r => hsInner Y W) hz
    have hflat : flatten Z = f Y • flatten (commutatorJ X Y) -
        f (commutatorJ X Y) • flatten Y := by
      apply PiLp.ext
      intro ij
      rfl
    simp only [hsInner, hflat, inner_sub_right, inner_smul_right, flatten_zero,
      inner_zero_right] at hinner
    have ho : inner ℂ (flatten Y) (flatten (commutatorJ X Y)) = 0 := horth
    rw [ho, mul_zero, zero_sub, neg_eq_zero] at hinner
    have hyy : inner ℂ (flatten Y) (flatten Y) ≠ 0 := by
      intro h
      have hy : flatten Y = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp h
      exact hY (flatten_injective (hy.trans flatten_zero.symm))
    have hfJ : f (commutatorJ X Y) = 0 := (mul_eq_zero.mp hinner).resolve_right hyy
    have hsmul : f Y • commutatorJ X Y = 0 := by simpa only [Z, hfJ, zero_smul, sub_zero] using hz
    exact hJ ((smul_eq_zero.mp hsmul).resolve_left hfY)
  refine ⟨Z, hZ, ?_, ?_⟩
  · have h := (commutatorTLinear X).map_sub (f Y • commutatorJ X Y)
      (f (commutatorJ X Y) • Y)
    simp only [map_smul, commutatorTLinear_apply, heigJ, heig] at h
    simpa only [Z, smul_sub, smul_comm (f Y) (lam : ℂ),
      smul_comm (f (commutatorJ X Y)) (lam : ℂ)] using h
  · simp only [Z, map_sub, map_smul, smul_eq_mul, mul_comm, sub_self]

#print axioms positive_eigenvector_pair
#assert_trust kernel positive_eigenvector_pair
#print axioms eigenspace_functional_kernel
#assert_trust kernel eigenspace_functional_kernel

end
end NLA.MI13

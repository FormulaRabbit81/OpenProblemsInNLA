/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.

The full generalized eigenspace decomposition is used; no eigenbasis or
simple interior spectrum is assumed. The Stein matrix need not be Hermitian.
-/
import NLA.MF18.GeneralizedStein
import NLA.MF18.StableDimension

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace NLA.MF18

theorem maxGenEigenspace_matrix_annihilation {n : ℕ} (S : Mat n) (lam : ℂ) (v : Vec n)
    (hv : v ∈ (Module.End.maxGenEigenspace S.toLin') lam) :
    ∃ k : ℕ, ((S - lam • (1 : Mat n)) ^ k).mulVec v = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace S.toLin' lam v).mp hv
  refine ⟨k, ?_⟩
  -- Matrix.toLin' applies by mulVec; expose the linear map so its algebra-hom power rules apply.
  change (((S - lam • (1 : Mat n)) ^ k).toLin') v = 0
  rw [Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one]
  exact hk

theorem pairing_separates_right {n : ℕ} (H : Mat n) (v : Vec n)
    (h : ∀ w : Vec n, pairing H w v = 0) : H.mulVec v = 0 := by
  classical
  ext i
  have he := h (Pi.single i 1)
  simpa only [pairing_eq_dotProduct, Pi.star_single, star_one,
    single_one_dotProduct, Pi.zero_apply] using he

theorem stable_space_in_kernel {n : ℕ} (S H : Mat n)
    (hweak : WeakStable S) (hstein : H = S.conjTranspose * H * S) :
    stableSubspace S ≤ LinearMap.ker H.toLin' := by
  classical
  apply iSup_le
  intro lam
  apply iSup_le
  intro hlam
  intro v hv
  -- Membership in ker H.toLin' unfolds to the zero matrix-vector product required by separation.
  change H.mulVec v = 0
  apply pairing_separates_right
  obtain ⟨l, hvpow⟩ := maxGenEigenspace_matrix_annihilation S lam v hv
  let W : Submodule ℂ (Vec n) :=
    { carrier := {w | pairing H w v = 0}
      zero_mem' := pairing_zero_left H v
      add_mem' := by
        intro w₁ w₂ hw₁ hw₂
        -- Unfold membership in the declared carrier of W for the sum of its two vectors.
        change pairing H (w₁ + w₂) v = 0
        rw [pairing_add_left, hw₁, hw₂, add_zero]
      smul_mem' := by
        intro a w hw
        -- Unfold the same carrier for scalar closure; the conjugate scalar still multiplies zero.
        change pairing H (a • w) v = 0
        rw [pairing_smul_left, hw, mul_zero] }
  have htop : (⊤ : Submodule ℂ (Vec n)) ≤ W := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top S.toLin']
    apply iSup_le
    intro μ
    intro w hw
    -- Membership in W is the annihilating-pairing condition to prove on each generalized eigenspace.
    change pairing H w v = 0
    by_cases hroot : μ ∈ S.charpoly.roots
    · have hμ : ‖μ‖ ≤ 1 := hweak μ (Polynomial.isRoot_of_mem_roots hroot)
      have hnorm : ‖star μ * lam‖ < 1 := by
        rw [norm_mul, norm_star]
        exact mul_lt_one_of_nonneg_of_lt_one_right hμ (norm_nonneg lam) hlam
      have hnonres : 1 - star μ * lam ≠ 0 := by
        intro he
        have hprod : star μ * lam = 1 := (sub_eq_zero.mp he).symm
        rw [hprod, norm_one] at hnorm
        exact lt_irrefl _ hnorm
      obtain ⟨k, hwpow⟩ := maxGenEigenspace_matrix_annihilation S μ w hw
      exact generalized_stein_pairing S H μ lam hstein hnonres k l w v hwpow hvpow
    · have hw0 : w = 0 := by
        rw [maxGenEigenspace_eq_bot_of_not_root S μ hroot] at hw
        exact hw
      rw [hw0, pairing_zero_left]
  intro w
  exact htop (Submodule.mem_top)

#print axioms stable_space_in_kernel

end NLA.MF18

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original IE-02 mathematical and library
attribution is retained in Definitions.lean and SourceCorrespondence.md.
Reuses Mathlib's complex scalar norm and continuous-linear operator-norm APIs.

Normalization uses the actual positive operator norm. The full maximal kernel
and the same degree-bounded polynomial parameters are transported back to T.
-/
import NLA.IE02.FiniteSchur

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE02
noncomputable section

theorem euclideanCLM_smul {n : ℕ} (c : ℂ) (A : Square n) :
    euclideanCLM (c • A) = c • euclideanCLM A := by
  apply ContinuousLinearMap.ext
  intro x
  -- The continuous extension has exactly the underlying Euclidean linear action.
  change euclideanLin (c • A) x = c • euclideanLin A x
  exact euclideanLin_smul_apply c A x

theorem operatorNorm_smul {n : ℕ} (c : ℂ) (A : Square n) :
    operatorNorm (c • A) = ‖c‖ * operatorNorm A := by
  -- This norm_smul is applied to continuous linear maps, not the ambient Matrix norm.
  simp only [operatorNorm, euclideanCLM_smul, norm_smul]

theorem scaled_maximal_factorization {n : ℕ} (hn : 1 ≤ n) (T : Square n)
    (hT : IsToeplitz T) (hne : T ≠ 0) :
    ∃ (d : ℕ) (a b : Poly),
      SchurPair n ((operatorNorm T : ℂ)⁻¹ • T) d a b ∧
      (∀ x : H n, x ∈ maximalSpace T ↔
        ∃ h : Poly, DegreeLE h (n - 1 - d) ∧ x = coeffVector n (b * h)) ∧
      (∀ h : Poly, DegreeLE h (n - 1 - d) →
        euclideanLin T (coeffVector n (b * h)) =
          (operatorNorm T : ℂ) • coeffVector n (a * h)) := by
  let M : ℝ := operatorNorm T
  have hnorm := euclidean_norm_attainment hn T
  have hMnonneg : 0 ≤ M := hnorm.1
  have hMne : M ≠ 0 := fun h => hne (hnorm.2.1.mp h)
  have hMpos : 0 < M := lt_of_le_of_ne hMnonneg hMne.symm
  have hMC : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMne
  let U : Square n := (M : ℂ)⁻¹ • T
  have hU : IsToeplitz U := by
    obtain ⟨p, hp⟩ := hT
    refine ⟨(M : ℂ)⁻¹ • p, ?_⟩
    dsimp only [U]
    rw [hp, toeplitz_smul]
  have hUnorm : operatorNorm U = 1 := by
    dsimp only [U]
    rw [operatorNorm_smul, norm_inv, Complex.norm_of_nonneg hMpos.le]
    exact inv_mul_cancel₀ hMne
  have hscale : T = (M : ℂ) • U := by
    simp only [U, smul_smul, mul_inv_cancel₀ hMC, one_smul]
  have haction (x : H n) : euclideanLin T x = (M : ℂ) • euclideanLin U x := by
    rw [hscale, euclideanLin_smul_apply]
  have hnormaction (x : H n) : ‖euclideanLin T x‖ = M * ‖euclideanLin U x‖ := by
    rw [haction, norm_smul, Complex.norm_of_nonneg hMpos.le]
  have hmem (x : H n) : x ∈ maximalSpace T ↔ x ∈ maximalSpace U := by
    rw [(maximal_space_norm T).2 x, maximal_space_norm_one U hUnorm x, hnormaction]
    constructor
    · exact mul_left_cancel₀ hMne
    · intro hx
      rw [hx]
  obtain ⟨d, a, b, hpair⟩ := finite_schur_boundary hn U hU hUnorm
  have hproperties := hpair
  rcases hproperties with ⟨_hd, _ha, _hb, _hb0, _hab, _hdisk, _hcircle,
    _hinterp, hparam, hparamaction, _hdim⟩
  refine ⟨d, a, b, hpair, ?_, ?_⟩
  · intro x
    exact (hmem x).trans (hparam x)
  · intro h hh
    rw [haction, hparamaction h hh]

#print axioms scaled_maximal_factorization
#assert_trust kernel scaled_maximal_factorization

end
end NLA.IE02

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Nobori's original question, Audenaert's
refined commutator theorem, and the repository reduction retain their attribution.

The actual Euclidean operator norm is the largest singular value, for every
complex rectangular matrix, including either empty dimension. The proof uses
the Gram eigenbasis directly, independently of full SVD or rectangular padding.
-/
import NLA.MI13.SingularSemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI13
noncomputable section
open scoped BigOperators

theorem operator_norm_semantics {m n : ℕ} (A : Rect m n) :
    spectralNorm A = singularValue A 0 ∧
    (spectralNorm A = 0 ↔ A = 0) ∧
    ∀ x : EuclideanVector n, ‖euclideanCLM A x‖ ≤ spectralNorm A * ‖x‖ := by
  classical
  have hs := singular_values_semantics A
  refine ⟨?_, ?_, fun x => (euclideanCLM A).le_opNorm x⟩
  · let hn := finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n)
    let b := (euclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis hn
    have hcoord (x : EuclideanVector n) (i : Fin n) :
        b.repr ((LinearMap.adjoint (euclideanLin A) ∘ₗ euclideanLin A) x) i =
          (singularValue A i.val : ℂ) ^ 2 * b.repr x i := by
      have h := (euclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis_apply_self_apply
        hn x i
      rw [← (euclideanLin A).sq_singularValues_fin hn i] at h
      simpa only [b, singularValue, RCLike.ofReal_eq_complex_ofReal,
        Complex.ofReal_pow] using h
    -- In the ordered Gram basis the image energy is the sum of the
    -- squared singular values weighted by the squared coordinates.
    have henergy (x : EuclideanVector n) :
        ‖euclideanLin A x‖ ^ 2 =
          ∑ i : Fin n, singularValue A i.val ^ 2 * ‖b.repr x i‖ ^ 2 := by
      calc
        ‖euclideanLin A x‖ ^ 2 =
            (inner ℂ x ((LinearMap.adjoint (euclideanLin A) ∘ₗ euclideanLin A) x)).re := by
          rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
          exact norm_sq_eq_re_inner (𝕜 := ℂ) (euclideanLin A x)
        _ = (inner ℂ (b.repr x)
            (b.repr ((LinearMap.adjoint (euclideanLin A) ∘ₗ euclideanLin A) x))).re :=
          congrArg Complex.re (b.repr.inner_map_map x
            ((LinearMap.adjoint (euclideanLin A) ∘ₗ euclideanLin A) x)).symm
        _ = ∑ i : Fin n, singularValue A i.val ^ 2 * ‖b.repr x i‖ ^ 2 := by
          rw [PiLp.inner_apply, Complex.re_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoord x i]
          -- Complex multiplication is its scalar action on ℂ, exposing
          -- the second argument for the linearity law inner_smul_right.
          change (inner ℂ (b.repr x i)
            (((singularValue A i.val : ℂ) ^ 2) • b.repr x i)).re = _
          rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
          simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
            ← Complex.ofReal_mul, Complex.ofReal_re]
    apply le_antisymm
    · -- Bound every vector using the largest Gram eigenvalue, then apply
      -- the CLM norm interface to the defining operator norm.
      change ‖euclideanCLM A‖ ≤ singularValue A 0
      apply (euclideanCLM A).opNorm_le_bound (hs.1 0)
      intro x
      apply (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (hs.1 0) (norm_nonneg _))).mp
      -- The finite-dimensional continuous extension has exactly the
      -- original linear-map action used by the energy identity.
      change ‖euclideanLin A x‖ ^ 2 ≤ (singularValue A 0 * ‖x‖) ^ 2
      rw [henergy x, mul_pow]
      calc
        ∑ i : Fin n, singularValue A i.val ^ 2 * ‖b.repr x i‖ ^ 2 ≤
            ∑ i : Fin n, singularValue A 0 ^ 2 * ‖b.repr x i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact (sq_le_sq₀ (hs.1 i.val) (hs.1 0)).mpr
            (hs.2.1 (Nat.zero_le i.val))
        _ = singularValue A 0 ^ 2 * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, b.repr.norm_map]
    · -- In an empty domain the singular values vanish. Otherwise the
      -- zeroth Gram basis vector attains the upper bound: its coordinates
      -- are the Euclidean single at zero, so the energy sum has one term.
      by_cases hn0 : n = 0
      · rw [hs.2.2 0 (by simpa only [hn0] using (le_refl (0 : ℕ)))]
        exact norm_nonneg (euclideanCLM A)
      · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn0⟩
        have hnorm : ‖euclideanLin A (b i)‖ = singularValue A 0 := by
          apply (sq_eq_sq₀ (norm_nonneg _) (hs.1 0)).mp
          simpa [PiLp.single_apply, apply_ite, mul_ite, i] using henergy (b i)
        calc
          singularValue A 0 = ‖euclideanCLM A (b i)‖ := hnorm.symm
          _ ≤ spectralNorm A * ‖b i‖ := (euclideanCLM A).le_opNorm (b i)
          _ = spectralNorm A := by rw [b.norm_eq_one, mul_one]
  · -- Norm definiteness and the two injective map conversions identify
    -- zero operator norm with the zero matrix, including empty dimensions.
    constructor
    · intro h
      have hclm : euclideanCLM A = 0 := norm_eq_zero.mp h
      have hlin : euclideanLin A = 0 := by
        apply LinearMap.toContinuousLinearMap.injective
        simpa only [euclideanCLM, map_zero] using hclm
      apply Matrix.toEuclideanLin.injective
      simpa only [euclideanLin, map_zero] using hlin
    · rintro rfl
      simp only [spectralNorm, euclideanCLM, euclideanLin, map_zero, norm_zero]

#print axioms operator_norm_semantics
#assert_trust kernel operator_norm_semantics

end
end NLA.MI13

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The non-annihilating word witnesses become uniform on the compact product of
the actual operator and vector unit spheres. The finite cover supplies both
the positive lower bound and a common maximum word length. Homogeneity then
extends the bridge bound to arbitrary operators and vectors, including zero.
-/
import NLA.MF06.IrreducibleOrbit
import NLA.MF06.CompactPositiveTests
import NLA.MF07.NormGeometry
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma irreducible_unit_bridge {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hirr : FamilyIrreducible M) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ T : EuclideanVector d →L[ℂ] EuclideanVector d, ‖T‖ = 1 →
        ∀ x : EuclideanVector d, ‖x‖ = 1 →
          ∃ w : List (Square d), WordIn M w ∧ w.length ≤ N ∧
            c ≤ ‖T (applyMatrix (matrixProduct w) x)‖ := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let : ProperSpace (EuclideanVector d →L[ℂ] EuclideanVector d) :=
    FiniteDimensional.proper ℂ _
  let J := {w : List (Square d) // WordIn M w}
  let K := Metric.sphere (0 : EuclideanVector d →L[ℂ] EuclideanVector d) 1 ×ˢ
    Metric.sphere (0 : EuclideanVector d) 1
  let f : J → ((EuclideanVector d →L[ℂ] EuclideanVector d) × EuclideanVector d) → ℝ :=
    fun w z => ‖z.1 (applyMatrix (matrixProduct w.val) z.2)‖
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hneK : K.Nonempty := by
    refine ⟨(ContinuousLinearMap.id ℂ (EuclideanVector d), coordinateUnit ⟨0, hd⟩), ?_⟩
    constructor
    · simp only [Metric.mem_sphere, dist_zero_right, ContinuousLinearMap.norm_id]
    · simp only [Metric.mem_sphere, dist_zero_right, coordinateUnit_norm]
  have hf (w : J) : Continuous (f w) :=
    (continuous_fst.clm_apply
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (matrixProduct w.val)).continuous.comp
        continuous_snd)).norm
  have hpos : ∀ z ∈ K, ∃ w : J, 0 < f w z := by
    intro z hz
    have hTnorm : ‖z.1‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz.1
    have hxnorm : ‖z.2‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
    have hT : z.1 ≠ 0 := by
      intro h
      exact zero_ne_one (by simpa only [h, norm_zero] using hTnorm)
    have hx : z.2 ≠ 0 := by
      intro h
      exact zero_ne_one (by simpa only [h, norm_zero] using hxnorm)
    obtain ⟨w, hw, hnonzero⟩ := irreducible_word_not_annihilated M hirr z.1 hT z.2 hx
    exact ⟨⟨w, hw⟩, norm_pos_iff.mpr hnonzero⟩
  obtain ⟨s, _, c, hc, hcover⟩ := compact_uniform_positive_tests K hK hneK f hf hpos
  refine ⟨s.sup (fun w => w.val.length), c, hc, ?_⟩
  intro T hT x hx
  have hp : (T, x) ∈ K := by
    constructor
    · simpa only [Metric.mem_sphere, dist_zero_right] using hT
    · simpa only [Metric.mem_sphere, dist_zero_right] using hx
  obtain ⟨w, hw, hcword⟩ := hcover (T, x) hp
  exact ⟨w.val, w.property, Finset.le_sup (f := fun w : J => w.val.length) hw, hcword⟩

/-- The bridge length and coefficient depend only on the fixed irreducible
family. The operator and vector are subsequently arbitrary. -/
lemma irreducible_bounded_bridge {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hirr : FamilyIrreducible M) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (T : EuclideanVector d →L[ℂ] EuclideanVector d) (x : EuclideanVector d),
        ∃ w : List (Square d), WordIn M w ∧ w.length ≤ N ∧
          c * ‖T‖ * ‖x‖ ≤ ‖T (applyMatrix (matrixProduct w) x)‖ := by
  obtain ⟨N, c, hc, hunit⟩ := irreducible_unit_bridge hd M hirr
  refine ⟨N, c, hc, ?_⟩
  intro T x
  by_cases hT : T = 0
  · refine ⟨[], WordIn_nil M, Nat.zero_le _, ?_⟩
    simp only [hT, norm_zero, mul_zero, zero_mul, zero_apply, le_refl]
  by_cases hx : x = 0
  · refine ⟨[], WordIn_nil M, Nat.zero_le _, ?_⟩
    simp only [hx, matrixProduct_nil, applyMatrix_one, norm_zero, mul_zero, map_zero, le_refl]
  have hTnorm : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let U : EuclideanVector d →L[ℂ] EuclideanVector d := (‖T‖⁻¹ : ℂ) • T
  let y : EuclideanVector d := (‖x‖⁻¹ : ℂ) • x
  have hU : ‖U‖ = 1 := by
    change ‖(‖T‖⁻¹ : ℂ) • T‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg T),
      inv_mul_cancel₀ hTnorm.ne']
  have hy : ‖y‖ = 1 := by
    change ‖(‖x‖⁻¹ : ℂ) • x‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg x),
      inv_mul_cancel₀ hxnorm.ne']
  obtain ⟨w, hw, hwN, hcw⟩ := hunit U hU y hy
  refine ⟨w, hw, hwN, ?_⟩
  have hscaled : ‖U (applyMatrix (matrixProduct w) y)‖ =
      ‖T‖⁻¹ * ‖x‖⁻¹ * ‖T (applyMatrix (matrixProduct w) x)‖ := by
    change ‖(‖T‖⁻¹ : ℂ) • T (applyMatrix (matrixProduct w) ((‖x‖⁻¹ : ℂ) • x))‖ = _
    rw [applyMatrix_smul_vector, T.map_smul, norm_smul, norm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg T),
      Real.norm_of_nonneg (norm_nonneg x)]
    ring
  rw [hscaled] at hcw
  calc
    c * ‖T‖ * ‖x‖ = (‖T‖ * ‖x‖) * c := by ring
    _ ≤ (‖T‖ * ‖x‖) * (‖T‖⁻¹ * ‖x‖⁻¹ * ‖T (applyMatrix (matrixProduct w) x)‖) :=
      mul_le_mul_of_nonneg_left hcw (mul_nonneg (norm_nonneg T) (norm_nonneg x))
    _ = (‖T‖ * ‖T‖⁻¹) * (‖x‖ * ‖x‖⁻¹) * ‖T (applyMatrix (matrixProduct w) x)‖ := by ring
    _ = ‖T (applyMatrix (matrixProduct w) x)‖ := by
      rw [mul_inv_cancel₀ hTnorm.ne', mul_inv_cancel₀ hxnorm.ne', one_mul, one_mul]

#print axioms irreducible_bounded_bridge
#assert_trust kernel irreducible_bounded_bridge

end NLA.MF06

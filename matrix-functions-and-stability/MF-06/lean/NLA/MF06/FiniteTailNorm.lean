/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

A finite sum of the already constructed tail seminorms supplies a norm that
strictly contracts on the stable subspace. This replaces a second discounted
infinite supremum by a symbolic finite sum; all tail indices remain arbitrary.
The contraction rate follows from an explicit loss of half the Euclidean norm.
-/
import NLA.MF06.StableKernel
import Mathlib.Analysis.Normed.Module.RCLike.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma norm_le_boundedEnvelope {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) : ‖x‖ ≤ boundedEnvelope M x := by
  obtain ⟨_, _, hbound⟩ := (bounded_envelope_norm M hM hneM hbounded).2.2.1
  exact (hbound x).1

lemma tailEnvelope_zero_index {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (x : EuclideanVector d) : tailEnvelope M 0 x = boundedEnvelope M x := by
  refine le_antisymm (tailEnvelope_le_boundedEnvelope M hM hneM hbounded 0 x) ?_
  simpa only [matrixProduct_nil, applyMatrix_one] using
    word_le_tailEnvelope M hM hneM hbounded 0 [] rfl (WordIn_nil M) x

/-- Homogeneity extends the actual unit-vector tail bound to every vector in S. -/
lemma tail_bound_of_unit_subspace {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (S : Submodule ℂ (EuclideanVector d)) (N : ℕ) (c : ℝ)
    (hunit : ∀ x : EuclideanVector d, x ∈ S → ‖x‖ = 1 → tailEnvelope M N x ≤ c)
    (x : EuclideanVector d) (hx : x ∈ S) : tailEnvelope M N x ≤ c * ‖x‖ := by
  by_cases hx0 : x = 0
  · subst x
    simp only [tailEnvelope_zero_vector M hM hneM hbounded, norm_zero, mul_zero, le_refl]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hscaled := hunit ((‖x‖⁻¹ : ℂ) • x) (S.smul_mem _ hx) (norm_smul_inv_norm hx0)
  have hscale : ‖x‖⁻¹ * tailEnvelope M N x ≤ c := by
    simpa only [tailEnvelope_smul M hM hneM hbounded, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg x)] using hscaled
  calc
    tailEnvelope M N x = ‖x‖ * (‖x‖⁻¹ * tailEnvelope M N x) := by
      rw [← mul_assoc, mul_inv_cancel₀ hnorm.ne', one_mul]
    _ ≤ ‖x‖ * c := mul_le_mul_of_nonneg_left hscale hnorm.le
    _ = c * ‖x‖ := mul_comm _ _

/-- A genuine Mathlib seminorm, obtained by summing the first N actual tails. -/
def finiteTailSeminorm {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (N : ℕ) : Seminorm ℂ (EuclideanVector d) :=
  ∑ k ∈ Finset.range N, tailSeminorm M hM hneM hbounded k

lemma finiteTailSeminorm_apply {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (N : ℕ) (x : EuclideanVector d) :
    finiteTailSeminorm M hM hneM hbounded N x = ∑ k ∈ Finset.range N, tailEnvelope M k x := by
  change FunLike.coeAddMonoidHom (Seminorm ℂ (EuclideanVector d)) (EuclideanVector d) ℝ
    (∑ k ∈ Finset.range N, tailSeminorm M hM hneM hbounded k) x = _
  simp only [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  rfl

lemma finiteTailSeminorm_continuous {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (N : ℕ) : Continuous (finiteTailSeminorm M hM hneM hbounded N : EuclideanVector d → ℝ) := by
  exact Seminorm.continuous_finsetSum (fun k _ => tailEnvelope_continuous M hM hneM hbounded k)

lemma finiteTailSeminorm_bounds {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (N : ℕ) (hN : 1 ≤ N) (K : ℝ)
    (hbound : ∀ x : EuclideanVector d, boundedEnvelope M x ≤ K * ‖x‖)
    (x : EuclideanVector d) :
    ‖x‖ ≤ finiteTailSeminorm M hM hneM hbounded N x ∧
      finiteTailSeminorm M hM hneM hbounded N x ≤ ((N : ℝ) * K) * ‖x‖ := by
  rw [finiteTailSeminorm_apply]
  constructor
  · calc
      ‖x‖ ≤ boundedEnvelope M x := norm_le_boundedEnvelope M hM hneM hbounded x
      _ = tailEnvelope M 0 x := (tailEnvelope_zero_index M hM hneM hbounded x).symm
      _ ≤ ∑ k ∈ Finset.range N, tailEnvelope M k x :=
        Finset.single_le_sum (fun k _ => tailEnvelope_nonneg M hM hneM hbounded k x)
          (Finset.mem_range.mpr (by omega))
  · calc
      (∑ k ∈ Finset.range N, tailEnvelope M k x) ≤ ∑ _k ∈ Finset.range N, K * ‖x‖ :=
        Finset.sum_le_sum (fun k _ => (tailEnvelope_le_boundedEnvelope M hM hneM hbounded k x).trans (hbound x))
      _ = ((N : ℝ) * K) * ‖x‖ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

lemma finiteTailSeminorm_step_loss {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (N : ℕ) (x : EuclideanVector d) (hsmall : tailEnvelope M N x ≤ ‖x‖ / 2)
    (A : Square d) (hA : A ∈ M) :
    finiteTailSeminorm M hM hneM hbounded N (applyMatrix A x) ≤
      finiteTailSeminorm M hM hneM hbounded N x - ‖x‖ / 2 := by
  have hstep : finiteTailSeminorm M hM hneM hbounded N (applyMatrix A x) ≤
      ∑ k ∈ Finset.range N, tailEnvelope M (k + 1) x := by
    rw [finiteTailSeminorm_apply]
    exact Finset.sum_le_sum (fun k _ => tailEnvelope_generator_le M hM hneM hbounded k A hA x)
  have hshift : (∑ k ∈ Finset.range N, tailEnvelope M (k + 1) x) + tailEnvelope M 0 x =
      finiteTailSeminorm M hM hneM hbounded N x + tailEnvelope M N x := by
    rw [finiteTailSeminorm_apply]
    exact (Finset.sum_range_succ' (fun k => tailEnvelope M k x) N).symm.trans
      (Finset.sum_range_succ (fun k => tailEnvelope M k x) N)
  have hzero : ‖x‖ ≤ tailEnvelope M 0 x := by
    rw [tailEnvelope_zero_index M hM hneM hbounded]
    exact norm_le_boundedEnvelope M hM hneM hbounded x
  linarith

/-- A genuine stable-coordinate norm with strict contraction on the prescribed
zero-limit subspace, constructed without a new infinite supremum. -/
theorem stable_coordinate_norm_exists {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (S : Submodule ℂ (EuclideanVector d))
    (hzero : ∀ x : EuclideanVector d, x ∈ S → stableGauge M x = 0) :
    ∃ u : Seminorm ℂ (EuclideanVector d), ∃ C q : ℝ,
      1 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧ Continuous (u : EuclideanVector d → ℝ) ∧
      (∀ x : EuclideanVector d, ‖x‖ ≤ u x ∧ u x ≤ C * ‖x‖) ∧
      (∀ A ∈ M, ∀ x : EuclideanVector d, x ∈ S → u (applyMatrix A x) ≤ q * u x) := by
  obtain ⟨N, hN, hsmall⟩ :=
    uniform_small_tail_on_subspace M hM hneM hbounded S hzero (1 / 2) (by norm_num)
  obtain ⟨K, hK, hbound⟩ := (bounded_envelope_norm M hM hneM hbounded).2.2.1
  let u := finiteTailSeminorm M hM hneM hbounded N
  let C : ℝ := (N : ℝ) * K
  let q : ℝ := 1 - 1 / (2 * C)
  have hC : 1 ≤ C := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp only [C]
    nlinarith
  have htwoC : 0 < 2 * C := by linarith
  have hq0 : 0 ≤ q := by
    have hdiv : (1 : ℝ) / (2 * C) ≤ 1 := (div_le_iff₀ htwoC).mpr (by linarith)
    dsimp only [q]
    linarith
  have hq1 : q < 1 := by
    have hdiv : (0 : ℝ) < 1 / (2 * C) := div_pos zero_lt_one htwoC
    dsimp only [q]
    linarith
  have hu : ∀ x : EuclideanVector d, ‖x‖ ≤ u x ∧ u x ≤ C * ‖x‖ :=
    finiteTailSeminorm_bounds M hM hneM hbounded N hN K (fun x => (hbound x).2)
  refine ⟨u, C, q, hC, hq0, hq1, finiteTailSeminorm_continuous M hM hneM hbounded N, hu, ?_⟩
  intro A hA x hx
  have hNx : tailEnvelope M N x ≤ ‖x‖ / 2 := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
      tail_bound_of_unit_subspace M hM hneM hbounded S N (1 / 2)
        (hsmall N le_rfl) x hx
  have hloss : u x / (2 * C) ≤ ‖x‖ / 2 := by
    apply (div_le_iff₀ htwoC).mpr
    nlinarith [(hu x).2]
  calc
    u (applyMatrix A x) ≤ u x - ‖x‖ / 2 :=
      finiteTailSeminorm_step_loss M hM hneM hbounded N x hNx A hA
    _ ≤ u x - u x / (2 * C) := sub_le_sub_left hloss _
    _ = q * u x := by dsimp only [q]; ring

#print axioms stable_coordinate_norm_exists
#assert_trust kernel stable_coordinate_norm_exists

end NLA.MF06

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

The reference cone estimates use the actual stable projection and quotient.
The off-diagonal bound follows by splitting a vector into its projected and
complementary parts; the first part contracts in the constructed finite-tail
norm. A proper stable kernel supplies an actual starting vector with first
component zero and quotient norm one. All constants depend only on M.
-/
import NLA.MF06.ComponentNorm
import NLA.MF06.FiniteTailNorm
import NLA.MF06.KernelExponential

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma reference_component_bound {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (u : Seminorm ℂ (EuclideanVector d)) (C q c : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ x : EuclideanVector d, u x ≤ C * ‖x‖)
    (hcontract : ∀ A ∈ M, ∀ x : EuclideanVector d,
      x ∈ stableKernel M hM hneM hbounded → u (applyMatrix A x) ≤ q * u x)
    (hcompl : ∀ x : EuclideanVector d,
      ‖x - (stableKernel M hM hneM hbounded).starProjection x‖ ≤ c * stableGauge M x)
    (A : Square d) (hA : A ∈ M) (x : EuclideanVector d) :
    stableComponentSeminorm M hM hneM hbounded u (applyMatrix A x) ≤
      q * stableComponentSeminorm M hM hneM hbounded u x +
        (C * familyNorm M * c) * stableGauge M x := by
  let S := stableKernel M hM hneM hbounded
  let a := stableComponentSeminorm M hM hneM hbounded u
  let s := S.starProjection x
  let y := x - s
  have hs : s ∈ S := S.starProjection_apply_mem x
  have hAs : applyMatrix A s ∈ S := stableKernel_invariant M hM hneM hbounded A hA s hs
  have hstable : a (applyMatrix A s) ≤ q * a x := by
    rw [stableComponentSeminorm_on_kernel M hM hneM hbounded u _ hAs]
    exact hcontract A hA s hs
  have hfamily := family_norm_maximum hd M hM hneM
  have hcross : a (applyMatrix A y) ≤ (C * familyNorm M * c) * stableGauge M x := by
    calc
      a (applyMatrix A y) ≤ C * ‖applyMatrix A y‖ :=
        stableComponentSeminorm_le M hM hneM hbounded u C hC hupper _
      _ ≤ C * (spectralNorm A * ‖y‖) :=
        mul_le_mul_of_nonneg_left (norm_applyMatrix_le A y) hC
      _ ≤ C * (familyNorm M * ‖y‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hfamily.2.2 A hA) (norm_nonneg y)) hC
      _ ≤ C * (familyNorm M * (c * stableGauge M x)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcompl x) hfamily.1) hC
      _ = (C * familyNorm M * c) * stableGauge M x := by ring
  have hsplit : x = s + y := by dsimp only [y]; abel
  calc
    a (applyMatrix A x) = a (applyMatrix A s + applyMatrix A y) := by
      rw [hsplit, applyMatrix_add_vector]
    _ ≤ a (applyMatrix A s) + a (applyMatrix A y) := map_add_le_add a _ _
    _ ≤ q * a x + (C * familyNorm M * c) * stableGauge M x := add_le_add hstable hcross

lemma cone_start_vector {d : ℕ} (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (hproper : stableKernel M hM hneM hbounded ≠ ⊤)
    (u : Seminorm ℂ (EuclideanVector d)) :
    ∃ x : EuclideanVector d,
      stableComponentSeminorm M hM hneM hbounded u x = 0 ∧ stableGauge M x = 1 := by
  let S := stableKernel M hM hneM hbounded
  obtain ⟨x, hx⟩ : ∃ x : EuclideanVector d, x ∉ S := by
    by_contra h
    apply hproper
    apply top_unique
    intro y _hy
    by_contra hy
    exact h ⟨y, hy⟩
  have hp : 0 < stableGauge M x := by
    have hp0 : stableGauge M x ≠ 0 := fun h => hx h
    exact lt_of_le_of_ne (apply_nonneg (stableSeminorm M hM hneM hbounded) x) hp0.symm
  let y := x - S.starProjection x
  have hy : stableGauge M y = stableGauge M x := stableGauge_complement M hM hneM hbounded x
  have hay : stableComponentSeminorm M hM hneM hbounded u y = 0 := by
    rw [stableComponentSeminorm_apply, stableProjection_complement, map_zero]
  have hscalar : ‖((stableGauge M x)⁻¹ : ℂ)‖ = (stableGauge M x)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hp.le]
  refine ⟨((stableGauge M x)⁻¹ : ℂ) • y, ?_, ?_⟩
  · rw [map_smul_eq_mul, hay, mul_zero]
  · rw [stableGauge_smul M hM hneM hbounded, hscalar, hy, inv_mul_cancel₀ hp.ne']

/-- All reference constants and the actual starting vector are chosen before
introducing any perturbing family. No invariant-subspace premise is placed on N. -/
theorem reference_cone_data {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hbounded : IsProductBounded M)
    (hradius : jointSpectralRadius M = 1) :
    ∃ a : Seminorm ℂ (EuclideanVector d), ∃ q K Ca Cb c : ℝ,
      0 ≤ q ∧ q < 1 ∧ 0 ≤ K ∧ 1 ≤ Ca ∧ 1 ≤ Cb ∧ 0 < c ∧
      (∀ x : EuclideanVector d,
        a x ≤ Ca * ‖x‖ ∧ stableGauge M x ≤ Cb * ‖x‖ ∧
          ‖x‖ ≤ c * (a x + stableGauge M x)) ∧
      (∀ A ∈ M, ∀ x : EuclideanVector d,
        a (applyMatrix A x) ≤ q * a x + K * stableGauge M x) ∧
      ∃ x : EuclideanVector d, a x = 0 ∧ stableGauge M x = 1 := by
  let S := stableKernel M hM hneM hbounded
  obtain ⟨S', hS', hproper', _hInv, _hdecay⟩ :=
    stable_kernel_exponential hd M hM hneM hbounded hradius
  have hSeq : S' = S := by
    ext x
    exact hS' x
  have hproper : S ≠ ⊤ := hSeq ▸ hproper'
  obtain ⟨u, Ca, q, hCa, hq0, hq1, hucont, hubound, hucontract⟩ :=
    stable_coordinate_norm_exists M hM hneM hbounded S (fun _ hx => hx)
  obtain ⟨Cb, hCb, hCbnd⟩ := (bounded_envelope_norm M hM hneM hbounded).2.2.1
  obtain ⟨c, hc, hcomp, hcompl⟩ :=
    component_norm_bounds hd M hM hneM hbounded u hucont (fun x => (hubound x).1)
  let a := stableComponentSeminorm M hM hneM hbounded u
  let K := Ca * familyNorm M * c
  have hCa0 : 0 ≤ Ca := zero_le_one.trans hCa
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg hCa0 (family_norm_maximum hd M hM hneM).1) hc.le
  refine ⟨a, q, K, Ca, Cb, c, hq0, hq1, hK, hCa, hCb, hc, ?_, ?_, ?_⟩
  · intro x
    exact ⟨stableComponentSeminorm_le M hM hneM hbounded u Ca hCa0 (fun y => (hubound y).2) x,
      (stableGauge_le_boundedEnvelope M hM hneM hbounded x).trans (hCbnd x).2, hcomp x⟩
  · intro A hA x
    exact reference_component_bound hd M hM hneM hbounded u Ca q c hCa0
      (fun y => (hubound y).2) hucontract hcompl A hA x
  · exact cone_start_vector M hM hneM hbounded hproper u

#print axioms reference_cone_data
#assert_trust kernel reference_cone_data

end NLA.MF06

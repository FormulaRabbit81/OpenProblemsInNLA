/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE17.Definitions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace NLA.IE17

lemma spectralNorm_eq_l2 {m n : ℕ} (E : Mat m n) : spectralNorm E = ‖E‖ := rfl

lemma spectralNorm_nonneg {m n : ℕ} (E : Mat m n) : 0 ≤ spectralNorm E := norm_nonneg _

lemma apply_norm_le {m n : ℕ} (E : Mat m n) (y : Vec n) :
    ‖E.toEuclideanLin y‖ ≤ spectralNorm E * ‖y‖ :=
  E.toEuclideanLin.toContinuousLinearMap.le_opNorm y

lemma spectralNorm_le_iff {m n : ℕ} (E : Mat m n) {c : ℝ} (hc : 0 ≤ c) :
    spectralNorm E ≤ c ↔ ∀ y : Vec n, ‖E.toEuclideanLin y‖ ≤ c * ‖y‖ := by
  constructor
  · intro h y
    exact (apply_norm_le E y).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  · intro h
    exact ContinuousLinearMap.opNorm_le_bound E.toEuclideanLin.toContinuousLinearMap hc h

lemma spectralNorm_transpose {m n : ℕ} (E : Mat m n) :
    spectralNorm E.transpose = spectralNorm E := by
  simpa only [spectralNorm_eq_l2, conjTranspose_eq_transpose_of_trivial] using
    Matrix.l2_opNorm_conjTranspose E

lemma transpose_apply_norm_le {m n : ℕ} (E : Mat m n) (u : Vec m) :
    ‖E.transpose.toEuclideanLin u‖ ≤ spectralNorm E * ‖u‖ := by
  simpa only [spectralNorm_transpose] using apply_norm_le E.transpose u

lemma feasible_neg {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    Feasible A b x (-A) := by
  simp [Feasible, normalResidual]

lemma feasible_zero_iff {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    Feasible A b x 0 ↔ normalResidual A b x = 0 := by
  simp [Feasible]

lemma error_nonneg {m n : ℕ} {A : Mat m n} {b : Vec m} {x : Vec n} {δ : ℝ}
    (h : IsOptimalError A b x δ) : 0 ≤ δ := by
  obtain ⟨E, _, rfl⟩ := h.1
  exact spectralNorm_nonneg E

lemma optimal_zero_of_normalResidual_zero {m n : ℕ} {A : Mat m n} {b : Vec m}
    {x : Vec n} (hx : normalResidual A b x = 0) : IsOptimalError A b x 0 := by
  refine ⟨⟨0, (feasible_zero_iff A b x).mpr hx, ?_⟩, ?_⟩
  · simp [spectralNorm]
  · intro δ hδ
    obtain ⟨E, _, rfl⟩ := hδ
    exact spectralNorm_nonneg E

lemma continuous_normalResidual_perturbation {m n : ℕ} (A : Mat m n) (b : Vec m)
    (x : Vec n) : Continuous (fun E : Mat m n => normalResidual (A + E) b x) := by
  have hL : Continuous (fun M : Mat m n => M.toEuclideanLin.toContinuousLinearMap) :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin n)).trans
      LinearMap.toContinuousLinearMap).toContinuousLinearEquiv.continuous
  have hT : Continuous (fun M : Mat n m => M.toEuclideanLin.toContinuousLinearMap) :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin m)).trans
      LinearMap.toContinuousLinearMap).toContinuousLinearEquiv.continuous
  have hplus : Continuous (fun E : Mat m n => A + E) := continuous_const.add continuous_id
  have ht : Continuous (fun E : Mat m n => (A + E).transpose) := by fun_prop
  exact (hT.comp ht).clm_apply (continuous_const.sub
    ((hL.comp hplus).clm_apply continuous_const))

lemma isClosed_feasible {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    IsClosed {E : Mat m n | Feasible A b x E} := by
  exact isClosed_eq (continuous_normalResidual_perturbation A b x) continuous_const

/-- The actual all-perturbation minimum is attained, including rectangular and degenerate inputs. -/
lemma exists_optimal_error {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    ∃ δ : ℝ, IsOptimalError A b x δ := by
  let S : Set (Mat m n) := {E | Feasible A b x E}
  let T := Metric.closedBall (0 : Mat m n) ‖A‖ ∩ S
  have hcompact : IsCompact T := (isCompact_closedBall 0 ‖A‖).inter_right
    (isClosed_feasible A b x)
  have hneg : -A ∈ T := by
    exact ⟨by simp [Metric.mem_closedBall], feasible_neg A b x⟩
  obtain ⟨E₀, hE₀, hmin⟩ := hcompact.exists_isMinOn ⟨-A, hneg⟩ continuous_norm.continuousOn
  refine ⟨spectralNorm E₀, ⟨⟨E₀, hE₀.2, rfl⟩, ?_⟩⟩
  intro δ hδ
  obtain ⟨E, hE, rfl⟩ := hδ
  change ‖E₀‖ ≤ ‖E‖
  by_cases hbound : ‖E‖ ≤ ‖A‖
  · apply hmin
    exact ⟨by simpa [Metric.mem_closedBall] using hbound, hE⟩
  · have h₀ : ‖E₀‖ ≤ ‖A‖ := by
      simpa [Metric.mem_closedBall] using hE₀.1
    exact h₀.trans (le_of_lt (lt_of_not_ge hbound))

end NLA.IE17

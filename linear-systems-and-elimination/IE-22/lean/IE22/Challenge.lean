import NLA.RowDeletion.Definitions

/-! IE-22 target signatures only. The deliberate placeholders are confined to
this challenge; proofs must import shared library modules instead. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace NLA.IE22
open NLA.RowDeletion

/-- Stronger than the canonical upper bound: no aspect-ratio restriction. -/
theorem eventual_uniform_upper
    {θ a : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (ha : GaussianCutoff θ a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ m n : ℕ, 0 < m → N ≤ n →
      ∀ A : Rows m n, UnitRows A →
        normalizedDeletion θ A ≤ Real.sqrt (gaussianTrimmedMoment a) + ε := by sorry

/-- The canonical supremum and its exact eventual-uniform quantifiers. -/
theorem extremal_eventual_uniform_upper
    {θ a : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (ha : GaussianCutoff θ a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N R : ℕ, 0 < N ∧ 0 < R ∧
      ∀ m n : ℕ, 0 < m → N ≤ n → (R : ℝ) ≤ (m : ℝ) / n →
        extremalDeletion θ m n ≤ Real.sqrt (gaussianTrimmedMoment a) + ε := by sorry

/-- Every strictly smaller candidate fails the eventual-uniform property,
with a fixed positive gap and a concrete unit-row witness beyond each pair of cutoffs. -/
theorem sharp_constant
    {θ a : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (ha : GaussianCutoff θ a)
    {c : ℝ} (hc : c < Real.sqrt (gaussianTrimmedMoment a)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N R : ℕ,
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ N ≤ n ∧ (R : ℝ) ≤ (m : ℝ) / n ∧
        ∃ A : Rows m n, UnitRows A ∧ c + ε < normalizedDeletion θ A := by sorry

theorem extremalDeletion_tendsto
    {θ a : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (ha : GaussianCutoff θ a)
    (m n : ℕ → ℕ) (hdim : ∀ j, 0 < m j ∧ 0 < n j)
    (hn : Tendsto n atTop atTop)
    (hr : Tendsto (fun j ↦ (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j ↦ extremalDeletion θ (m j) (n j)) atTop
      (𝓝 (Real.sqrt (gaussianTrimmedMoment a))) := by sorry

end NLA.IE22

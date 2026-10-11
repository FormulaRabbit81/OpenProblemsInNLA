import NLA.RowDeletion.DeterministicWitness

/-! # The IE-21 to IE-22 transfer

These are proved implications. The concentration and uniform upper-bound
hypotheses are explicit: their analytic proofs remain separate work. The
shared variational definitions and witness extraction are imported from IE-21.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace NLA.IE22
open RowDeletion

theorem extremal_eventual_uniform_upper_of_uniform_upper
    {θ c : ℝ}
    (hupper : ∃ N : ℕ, 0 < N ∧ ∀ m n : ℕ, 0 < m → N ≤ n →
      ∀ A : Rows m n, UnitRows A → normalizedDeletion θ A ≤ c) :
    ∃ N R : ℕ, 0 < N ∧ 0 < R ∧ ∀ m n : ℕ, 0 < m → N ≤ n →
      (R : ℝ) ≤ (m : ℝ) / n → extremalDeletion θ m n ≤ c := by
  obtain ⟨N, hN, hupper⟩ := hupper
  refine ⟨N, 1, hN, by omega, ?_⟩
  intro m n hm hn _
  exact extremalDeletion_le (hN.trans_le hn) θ c (hupper m n hm hn)

/-- Sharpness needs concentration only along the single diagonal `m=n²`. -/
theorem sharp_constant_of_diagonal_concentration
    {θ a : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hconcentration : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun j : ℕ ↦ (sphericalRowsLaw ((j + 1) ^ 2) (j + 1)).real
        {A | ε < |normalizedTrimmedEnergy θ A - gaussianTrimmedMoment a|}) atTop (𝓝 0))
    {c : ℝ} (hc : c < Real.sqrt (gaussianTrimmedMoment a)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N R : ℕ,
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ N ≤ n ∧ (R : ℝ) ≤ (m : ℝ) / n ∧
        ∃ A : Rows m n, UnitRows A ∧ c + ε < normalizedDeletion θ A := by
  let b := max 0 ((c + Real.sqrt (gaussianTrimmedMoment a)) / 2)
  by_cases hcneg : c < 0
  · refine ⟨-c / 2, by linarith, ?_⟩
    intro N R
    let n := max N R + 1
    have hn : 0 < n := by dsimp [n]; omega
    obtain ⟨A, hA⟩ := unitRows_exists (n ^ 2) hn
    refine ⟨n ^ 2, n, by positivity, hn, by dsimp [n]; omega, ?_, A, hA, ?_⟩
    · have he : ((n ^ 2 : ℕ) : ℝ) / n = n := by
        push_cast
        field_simp
      rw [he]
      exact_mod_cast (show R ≤ n by dsimp [n]; omega)
    · have := normalizedDeletion_nonneg hn hθ₁ A
      linarith
  · have hc₀ := le_of_not_gt hcneg
    have hb₀ : 0 ≤ b := le_max_left _ _
    have hcb : c < b := by dsimp [b]; exact lt_max_of_lt_right (by linarith)
    have hb : b < Real.sqrt (gaussianTrimmedMoment a) := by
      dsimp [b]
      exact max_lt (by linarith) (by linarith)
    have hbsq : b ^ 2 < gaussianTrimmedMoment a := by
      nlinarith [Real.sq_sqrt (gaussianTrimmedMoment_nonneg a)]
    have hw := eventually_exists_unitRows_large_of_concentration hθ₀ hθ₁ hb₀ hbsq
      (fun j ↦ (j + 1) ^ 2) (fun j ↦ j + 1) (fun j ↦ Nat.succ_pos j) hconcentration
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hw
    refine ⟨(b - c) / 2, by linarith, ?_⟩
    intro N R
    let j := max J (max N R)
    have hj : J ≤ j := le_max_left _ _
    obtain ⟨A, hA, hvalue⟩ := hJ j hj
    refine ⟨(j + 1) ^ 2, j + 1, by positivity, by omega,
      by dsimp [j]; omega, ?_, A, hA, by linarith⟩
    have he : (((j + 1) ^ 2 : ℕ) : ℝ) / (j + 1 : ℕ) = (j + 1 : ℕ) := by
      push_cast
      field_simp
    rw [he]
    exact_mod_cast (show R ≤ j + 1 by dsimp [j]; omega)

theorem extremalDeletion_tendsto_of_concentration_and_uniform_upper
    {θ a : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (m n : ℕ → ℕ) (hdim : ∀ j, 0 < m j ∧ 0 < n j) (hn : Tendsto n atTop atTop)
    (hconcentration : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun j ↦ (sphericalRowsLaw (m j) (n j)).real
        {A | ε < |normalizedTrimmedEnergy θ A - gaussianTrimmedMoment a|}) atTop (𝓝 0))
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      ∀ m n : ℕ, 0 < m → N ≤ n → ∀ A : Rows m n, UnitRows A →
        normalizedDeletion θ A ≤ Real.sqrt (gaussianTrimmedMoment a) + ε) :
    Tendsto (fun j ↦ extremalDeletion θ (m j) (n j)) atTop
      (𝓝 (Real.sqrt (gaussianTrimmedMoment a))) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    by_cases hc₀ : 0 ≤ c
    · have hsq : c ^ 2 < gaussianTrimmedMoment a := by
        nlinarith [Real.sq_sqrt (gaussianTrimmedMoment_nonneg a)]
      filter_upwards [eventually_exists_unitRows_large_of_concentration hθ₀ hθ₁ hc₀ hsq
        m n (fun j ↦ (hdim j).2) hconcentration] with j hj
      obtain ⟨A, hA, hcA⟩ := hj
      exact hcA.trans_le (normalizedDeletion_le_extremal (hdim j).1 (hdim j).2 hθ₀ hθ₁ hA)
    · filter_upwards with j
      obtain ⟨A, hA⟩ := unitRows_exists (m j) (hdim j).2
      exact (lt_of_not_ge hc₀).trans_le ((normalizedDeletion_nonneg (hdim j).2 hθ₁ A).trans
        (normalizedDeletion_le_extremal (hdim j).1 (hdim j).2 hθ₀ hθ₁ hA))
  · intro c hc
    obtain ⟨N, _, hN⟩ := hupper ((c - Real.sqrt (gaussianTrimmedMoment a)) / 2) (by linarith)
    filter_upwards [hn.eventually (eventually_ge_atTop N)] with j hj
    have h := extremalDeletion_le (hdim j).2 θ _ (hN (m j) (n j) (hdim j).1 hj)
    linarith

end NLA.IE22

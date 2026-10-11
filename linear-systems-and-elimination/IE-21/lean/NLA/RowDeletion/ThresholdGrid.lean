import NLA.RowDeletion.Trimming

/-! # A finite threshold grid with explicit cardinality

The grid includes zero and stays inside the cutoff interval. Its covering and
cardinality estimates are reused by the random and deterministic arguments.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NLA.RowDeletion

theorem exists_threshold_grid {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 < ρ) :
    ∃ T : Finset ℝ, (∀ t ∈ T, t ∈ Set.Icc 0 L) ∧
      (T.card : ℝ) ≤ L / ρ + 1 ∧
      ∀ t ∈ Set.Icc 0 L, ∃ s ∈ T, |t - s| ≤ ρ := by
  classical
  let K := ⌊L / ρ⌋₊
  let T := (Finset.range (K + 1)).image (fun i : ℕ ↦ (i : ℝ) * ρ)
  have hfloor : (K : ℝ) * ρ ≤ L := by
    exact (le_div_iff₀ hρ).mp (Nat.floor_le (div_nonneg hL hρ.le))
  refine ⟨T, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hiK : i ≤ K := by simpa using Finset.mem_range.mp hi
    exact ⟨by positivity,
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hiK) hρ.le).trans hfloor⟩
  · calc
      (T.card : ℝ) ≤ ((Finset.range (K + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      _ = (K : ℝ) + 1 := by simp
      _ ≤ L / ρ + 1 := by
        have := Nat.floor_le (div_nonneg hL hρ.le)
        dsimp [K]
        linarith
  · intro t ht
    let i := ⌊t / ρ⌋₊
    have hiK : i ≤ K := Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hρ.le)
    have hlow : (i : ℝ) * ρ ≤ t :=
      (le_div_iff₀ hρ).mp (Nat.floor_le (div_nonneg ht.1 hρ.le))
    have hupp : t < ((i : ℝ) + 1) * ρ :=
      (div_lt_iff₀ hρ).mp (Nat.lt_floor_add_one (t / ρ))
    refine ⟨(i : ℝ) * ρ, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
    nlinarith

/-- Two 1-Lipschitz objectives need only be compared on the same finite grid. -/
theorem abs_sub_le_of_threshold_grid
    {L ρ η : ℝ} {T : Finset ℝ} (hT : ∀ s ∈ T, s ∈ Set.Icc 0 L)
    (hcover : ∀ t ∈ Set.Icc 0 L, ∃ s ∈ T, |t - s| ≤ ρ)
    {f g : ℝ → ℝ}
    (hf : ∀ s ∈ Set.Icc 0 L, ∀ t ∈ Set.Icc 0 L, |f s - f t| ≤ |s - t|)
    (hg : ∀ s ∈ Set.Icc 0 L, ∀ t ∈ Set.Icc 0 L, |g s - g t| ≤ |s - t|)
    (hgrid : ∀ s ∈ T, |f s - g s| ≤ η) {t : ℝ} (ht : t ∈ Set.Icc 0 L) :
    |f t - g t| ≤ η + 2 * ρ := by
  obtain ⟨s, hs, hdist⟩ := hcover t ht
  have hfs := (hf t ht s (hT s hs)).trans hdist
  have hgs := hg s (hT s hs) t ht
  rw [abs_sub_comm s t] at hgs
  have hgs' := hgs.trans hdist
  have hfg := hgrid s hs
  have h₁ := abs_sub_le (f t) (f s) (g t)
  have h₂ := abs_sub_le (f s) (g s) (g t)
  linarith

end NLA.RowDeletion

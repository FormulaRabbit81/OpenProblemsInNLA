import NLA.RowDeletion.Definitions
import Mathlib.Topology.Order.Monotone
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! # Variational semantics and degenerate cases

The square bridge uses continuity and monotonicity of square root on infima.
It does not need an SVD or a separate interchange of two minimizing operations.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NLA.RowDeletion

lemma retainedCount_le {θ : ℝ} (hθ : θ ≤ 1) (m : ℕ) : retainedCount θ m ≤ m := by
  apply Nat.floor_le_of_le
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

lemma exists_unit_vector {n : ℕ} (hn : 0 < n) : ∃ x : Vector n, ‖x‖ = 1 := by
  exact ⟨EuclideanSpace.basisFun (Fin n) ℝ ⟨0, hn⟩,
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one _⟩

lemma retainedEnergy_nonneg {m n : ℕ} (A : Rows m n) (S : Finset (Fin m))
    (x : Vector n) : 0 ≤ retainedEnergy A S x :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma retainedValues_nonempty {m n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ : θ ≤ 1) (A : Rows m n) :
    {v : ℝ | ∃ S : Finset (Fin m), S.card = retainedCount θ m ∧
      ∃ x : Vector n, ‖x‖ = 1 ∧ v = retainedEnergy A S x}.Nonempty := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show retainedCount θ m ≤ (Finset.univ : Finset (Fin m)).card by
      simpa using retainedCount_le hθ m)
  obtain ⟨x, hx⟩ := exists_unit_vector hn
  exact ⟨retainedEnergy A S x, S, hS, x, hx, rfl⟩

lemma retainedValues_bddBelow {m n : ℕ} (θ : ℝ) (A : Rows m n) :
    BddBelow {v : ℝ | ∃ S : Finset (Fin m), S.card = retainedCount θ m ∧
      ∃ x : Vector n, ‖x‖ = 1 ∧ v = retainedEnergy A S x} := by
  refine ⟨0, ?_⟩
  rintro v ⟨S, _, x, _, rfl⟩
  exact retainedEnergy_nonneg A S x

theorem trimmedEnergy_nonneg {m n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ : θ ≤ 1) (A : Rows m n) : 0 ≤ trimmedEnergy θ A := by
  apply le_csInf (retainedValues_nonempty hn hθ A)
  rintro v ⟨S, _, x, _, rfl⟩
  exact retainedEnergy_nonneg A S x

theorem trimmedEnergy_le {m n : ℕ} (θ : ℝ) (A : Rows m n)
    {S : Finset (Fin m)} (hS : S.card = retainedCount θ m)
    {x : Vector n} (hx : ‖x‖ = 1) :
    trimmedEnergy θ A ≤ retainedEnergy A S x :=
  csInf_le (retainedValues_bddBelow θ A) ⟨S, hS, x, hx, rfl⟩

theorem deletionSingularValue_eq_sqrt {m n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ : θ ≤ 1) (A : Rows m n) :
    deletionSingularValue θ A = Real.sqrt (trimmedEnergy θ A) := by
  have he : Real.sqrt '' {v : ℝ | ∃ S : Finset (Fin m), S.card = retainedCount θ m ∧
      ∃ x : Vector n, ‖x‖ = 1 ∧ v = retainedEnergy A S x} =
      {v : ℝ | ∃ S : Finset (Fin m), S.card = retainedCount θ m ∧
        ∃ x : Vector n, ‖x‖ = 1 ∧ v = Real.sqrt (retainedEnergy A S x)} := by
    ext v
    constructor
    · rintro ⟨w, ⟨S, hS, x, hx, rfl⟩, rfl⟩
      exact ⟨S, hS, x, hx, rfl⟩
    · rintro ⟨S, hS, x, hx, rfl⟩
      exact ⟨retainedEnergy A S x, ⟨S, hS, x, hx, rfl⟩, rfl⟩
  unfold deletionSingularValue trimmedEnergy
  rw [← he]
  exact (Real.sqrt_monotone.map_csInf_of_continuousAt Real.continuous_sqrt.continuousAt
    (retainedValues_nonempty hn hθ A) (retainedValues_bddBelow θ A)).symm

/-- The internal squared quantity is exactly the square of the canonical variational one. -/
theorem deletionSingularValue_sq {m n : ℕ} (hn : 0 < n)
    {θ : ℝ} (_hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (A : Rows m n) :
    deletionSingularValue θ A ^ 2 = trimmedEnergy θ A := by
  rw [deletionSingularValue_eq_sqrt hn hθ₁]
  exact Real.sq_sqrt (trimmedEnergy_nonneg hn hθ₁ A)

theorem deletionSingularValue_nonneg {m n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ : θ ≤ 1) (A : Rows m n) : 0 ≤ deletionSingularValue θ A := by
  rw [deletionSingularValue_eq_sqrt hn hθ]
  exact Real.sqrt_nonneg _

theorem trimmedEnergy_eq_zero_of_retainedCount_eq_zero {m n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ : θ ≤ 1) (A : Rows m n) (hk : retainedCount θ m = 0) :
    trimmedEnergy θ A = 0 := by
  obtain ⟨x, hx⟩ := exists_unit_vector hn
  apply le_antisymm _ (trimmedEnergy_nonneg hn hθ A)
  have h := trimmedEnergy_le θ A (S := ∅) (by simpa using hk.symm) hx
  simpa [retainedEnergy] using h

theorem trimmedEnergy_eq_zero_of_unit_kernel {m n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ : θ ≤ 1) (A : Rows m n) {x : Vector n}
    (hx : ‖x‖ = 1) (hker : ∀ i, inner ℝ (A i) x = 0) : trimmedEnergy θ A = 0 := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show retainedCount θ m ≤ (Finset.univ : Finset (Fin m)).card by
      simpa using retainedCount_le hθ m)
  apply le_antisymm _ (trimmedEnergy_nonneg hn hθ A)
  have h := trimmedEnergy_le θ A hS hx
  simpa [retainedEnergy, hker] using h

@[simp]
theorem rowOperator_apply {m n : ℕ} (A : Rows m n) (x : Vector n) (i : Fin m) :
    rowOperator A x i = inner ℝ (A i) x := by
  change (∑ j, A i j * x j) = inner ℝ (A i) x
  simp [PiLp.inner_apply, mul_comm]

theorem retainedEnergy_univ {m n : ℕ} (A : Rows m n) (x : Vector n) :
    retainedEnergy A Finset.univ x = ‖rowOperator A x‖ ^ 2 := by
  simp [retainedEnergy, EuclideanSpace.real_norm_sq_eq, rowOperator_apply]

theorem retainedEnergy_le_card {m n : ℕ} {A : Rows m n} (hA : UnitRows A)
    (S : Finset (Fin m)) {x : Vector n} (hx : ‖x‖ = 1) :
    retainedEnergy A S x ≤ S.card := by
  have hentry (i : Fin m) : (inner ℝ (A i) x) ^ 2 ≤ 1 := by
    have h := abs_real_inner_le_norm (A i) x
    rw [hA i, hx, one_mul] at h
    nlinarith [abs_nonneg (inner ℝ (A i) x), sq_abs (inner ℝ (A i) x)]
  calc
    _ ≤ ∑ _i ∈ S, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hentry i
    _ = _ := by simp

theorem trimmedEnergy_le_retainedCount {m n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ : θ ≤ 1) {A : Rows m n} (hA : UnitRows A) :
    trimmedEnergy θ A ≤ retainedCount θ m := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show retainedCount θ m ≤ (Finset.univ : Finset (Fin m)).card by
      simpa using retainedCount_le hθ m)
  obtain ⟨x, hx⟩ := exists_unit_vector hn
  exact (trimmedEnergy_le θ A hS hx).trans (hS ▸ retainedEnergy_le_card hA S hx)

theorem operatorNorm_ge_one {m n : ℕ} (hm : 0 < m) {A : Rows m n}
    (hA : UnitRows A) : 1 ≤ operatorNorm A := by
  let i : Fin m := ⟨0, hm⟩
  have hc := PiLp.norm_apply_le (rowOperator A (A i)) i
  rw [rowOperator_apply, real_inner_self_eq_norm_sq, hA i] at hc
  have hop := (rowOperator A).le_opNorm (A i)
  simpa [operatorNorm, hA i] using (by simpa using hc : (1 : ℝ) ≤ ‖rowOperator A (A i)‖).trans hop

theorem normalizedDeletion_nonneg {m n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ : θ ≤ 1) (A : Rows m n) : 0 ≤ normalizedDeletion θ A :=
  mul_nonneg (Real.sqrt_nonneg _) (deletionSingularValue_nonneg hn hθ A)

theorem normalizedDeletion_sq {m n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (A : Rows m n) :
    normalizedDeletion θ A ^ 2 = normalizedTrimmedEnergy θ A := by
  rw [normalizedDeletion, mul_pow, Real.sq_sqrt (by positivity),
    deletionSingularValue_sq hn hθ₀ hθ₁]
  rfl

theorem normalizedDeletion_le_sqrt_dim {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) {A : Rows m n} (hA : UnitRows A) :
    normalizedDeletion θ A ≤ Real.sqrt n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hbound : trimmedEnergy θ A ≤ m :=
    (trimmedEnergy_le_retainedCount hn hθ₁ hA).trans (by exact_mod_cast retainedCount_le hθ₁ m)
  have hsq : normalizedDeletion θ A ^ 2 ≤ n := by
    rw [normalizedDeletion_sq hn hθ₀ hθ₁, normalizedTrimmedEnergy]
    calc
      _ ≤ (n : ℝ) / m * m := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = n := div_mul_cancel₀ _ hm'.ne'
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]

lemma unitRows_exists (m : ℕ) {n : ℕ} (hn : 0 < n) : ∃ A : Rows m n, UnitRows A := by
  obtain ⟨x, hx⟩ := exists_unit_vector hn
  exact ⟨fun _ ↦ x, fun _ ↦ hx⟩

lemma extremalValues_nonempty (θ : ℝ) (m : ℕ) {n : ℕ} (hn : 0 < n) :
    {v : ℝ | ∃ A : Rows m n, UnitRows A ∧ v = normalizedDeletion θ A}.Nonempty := by
  obtain ⟨A, hA⟩ := unitRows_exists m hn
  exact ⟨normalizedDeletion θ A, A, hA, rfl⟩

lemma extremalValues_bddAbove {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    BddAbove {v : ℝ | ∃ A : Rows m n, UnitRows A ∧ v = normalizedDeletion θ A} := by
  refine ⟨Real.sqrt n, ?_⟩
  rintro v ⟨A, hA, rfl⟩
  exact normalizedDeletion_le_sqrt_dim hm hn hθ₀ hθ₁ hA

theorem normalizedDeletion_le_extremal {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) {A : Rows m n} (hA : UnitRows A) :
    normalizedDeletion θ A ≤ extremalDeletion θ m n :=
  le_csSup (extremalValues_bddAbove hm hn hθ₀ hθ₁) ⟨A, hA, rfl⟩

/-- A pointwise uniform upper bound passes to the actual supremum. -/
theorem extremalDeletion_le {m n : ℕ} (hn : 0 < n) (θ c : ℝ)
    (hbound : ∀ A : Rows m n, UnitRows A → normalizedDeletion θ A ≤ c) :
    extremalDeletion θ m n ≤ c := by
  apply csSup_le (extremalValues_nonempty θ m hn)
  rintro v ⟨A, hA, rfl⟩
  exact hbound A hA

end NLA.RowDeletion

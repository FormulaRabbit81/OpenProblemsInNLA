/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted formalization of Colbrook's adjugate completion argument. -/
import NLA.IV03.Complementary
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma rank_le_one_two_minor_zero {n : ℕ} (H : Mat n) (hH : H.rank ≤ 1)
    (r c : Fin 2 → Fin n) : (H.submatrix r c).det = 0 := by
  by_contra hn
  have hr := Matrix.rank_of_det_ne_zero hn
  have hl := Matrix.rank_submatrix_le H r c
  simp only [Fintype.card_fin] at hr
  omega

lemma zMatrix_positive_diagonal_rank_gt_one {n : ℕ} (hn : 3 ≤ n)
    (H : Mat n) (hd : ∀ i, 0 < H i i)
    (hz : ∀ i j, i ≠ j → H i j ≤ 0) : 1 < H.rank := by
  by_contra hh
  have hRank : H.rank ≤ 1 := by omega
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; simp [b, c] at this
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; simp [a, c] at this
  have h₁ := rank_le_one_two_minor_zero H hRank ![a,b] ![a,b]
  have h₂ := rank_le_one_two_minor_zero H hRank ![b,c] ![b,c]
  have h₃ := rank_le_one_two_minor_zero H hRank ![a,b] ![b,c]
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at h₁ h₂ h₃
  have hprod₁ : 0 < H a a * H b b := mul_pos (hd a) (hd b)
  have hprod₂ : 0 < H b b * H c c := mul_pos (hd b) (hd c)
  have hx : H a b < 0 := by
    have hx₀ := hz a b hab
    have hy₀ := hz b a (Ne.symm hab)
    nlinarith
  have hy : H b c < 0 := by
    have hx₀ := hz b c hbc
    have hy₀ := hz c b (Ne.symm hbc)
    nlinarith
  have hpos := mul_pos_of_neg_of_neg hx hy
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (hz a c hac) (le_of_lt (hd b))
  nlinarith

/-- The singular case is excluded by a nonzero principal minor of codimension
one and the adjugate signs. No invertibility of A is assumed. -/
lemma adjugate_nonsingular {n : ℕ} (hn : 2 ≤ n) (A : Mat (n+1))
    (hminor : (A.submatrix (Fin.succ : Fin n → Fin (n+1)) Fin.succ).det ≠ 0)
    (hd : ∀ i, 0 < A.adjugate i i)
    (hz : ∀ i j, i ≠ j → A.adjugate i j ≤ 0) : A.det ≠ 0 := by
  intro hzero
  have hprod : A * A.adjugate = 0 := by rw [Matrix.mul_adjugate, hzero, zero_smul]
  have hr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hprod
  have hsub := Matrix.rank_submatrix_le A (Fin.succ : Fin n → Fin (n+1)) Fin.succ
  have hfull := Matrix.rank_of_det_ne_zero hminor
  have hbig := zMatrix_positive_diagonal_rank_gt_one (n := n+1) (by omega)
    A.adjugate hd hz
  simp only [Fintype.card_fin] at hr hfull
  omega

lemma adjugate_det_pos_of_diagonal {n : ℕ} (hn : 2 ≤ n) (A : Mat (n+1))
    (hp : ∀ m, m < n+1 → ∀ e : Fin m ↪ Fin (n+1), 0 < (A.submatrix e e).det)
    (hd : ∀ i, 0 < A.adjugate i i)
    (hz : ∀ i j, i ≠ j → A.adjugate i j ≤ 0) : 0 < A.det := by
  have hminor := hp n (by omega) (Fin.succEmb n)
  have hne := adjugate_nonsingular hn A (ne_of_gt hminor) hd hz
  by_contra hnot
  have hneg : A.det < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hne
  let e : Fin 3 ↪ Fin (n+1) := Fin.castLEEmb (by omega)
  let B : Mat 3 := (A⁻¹).submatrix e e
  have hBd : ∀ i, B i i < 0 := by
    intro i
    change A⁻¹ (e i) (e i) < 0
    rw [Matrix.inv_def]
    change Ring.inverse A.det * A.adjugate (e i) (e i) < 0
    rw [Ring.inverse_eq_inv]
    exact mul_neg_of_neg_of_pos (inv_lt_zero.mpr hneg) (hd (e i))
  have hBo : ∀ i j, i ≠ j → 0 ≤ B i j := by
    intro i j hij
    change 0 ≤ A⁻¹ (e i) (e j)
    rw [Matrix.inv_def]
    change 0 ≤ Ring.inverse A.det * A.adjugate (e i) (e j)
    rw [Ring.inverse_eq_inv]
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt (inv_lt_zero.mpr hneg))
      (hz (e i) (e j) (fun h => hij (e.injective h)))
  have hpair : ∀ i j : Fin 3, i ≠ j → B i i * B j j - B i j * B j i < 0 := by
    intro i j hij
    let f : Fin 2 ↪ Fin (n+1) := ⟨![e i, e j], by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all⟩
    have h := inverse_principal_det_neg A (by omega : 0 < 2) f hneg hp
    have hf0 : f 0 = e i := rfl
    have hf1 : f 1 = e j := rfl
    simpa only [B, Matrix.det_fin_two, Matrix.submatrix_apply, hf0, hf1] using h
  have hpos := threeByThree_negative_minors_det_pos B hBd hBo
    (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
  have hnegative := inverse_principal_det_neg A (by omega : 0 < 3) e hneg hp
  change B.det < 0 at hnegative
  linarith

/-- Full adjugate completion for order at least three: proper principal
minors positive and off-diagonal adjugate entries nonpositive force det A > 0.
In particular this theorem has no regularity premise. -/
lemma adjugate_completion {n : ℕ} (hn : 2 ≤ n) (A : Mat (n+1))
    (hp : ∀ m, m < n+1 → ∀ e : Fin m ↪ Fin (n+1), 0 < (A.submatrix e e).det)
    (hz : ∀ i j, i ≠ j → A.adjugate i j ≤ 0) : 0 < A.det := by
  apply adjugate_det_pos_of_diagonal hn A hp
  · intro i
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, ← two_mul, pow_mul]
    norm_num
    exact hp n (by omega) i.succAboveEmb
  · exact hz

lemma inverseM_of_proper_principal_and_adjugate {n : ℕ} (hn : 2 ≤ n)
    (A : Mat (n+1)) (hA : ∀ i j, 0 ≤ A i j)
    (hp : ∀ m, m < n+1 → ∀ e : Fin m ↪ Fin (n+1), 0 < (A.submatrix e e).det)
    (hz : ∀ i j, i ≠ j → A.adjugate i j ≤ 0) : IsInverseM A := by
  have hd := adjugate_completion hn A hp hz
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (ne_of_gt hd)), hA, ?_⟩
  intro i j hij
  rw [Matrix.inv_def]
  change Ring.inverse A.det * A.adjugate i j ≤ 0
  rw [Ring.inverse_eq_inv]
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hd)) (hz i j hij)

end NLA.IV03

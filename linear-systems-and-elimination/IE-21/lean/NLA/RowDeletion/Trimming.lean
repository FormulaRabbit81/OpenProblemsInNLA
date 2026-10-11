import NLA.RowDeletion.Definitions
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite trimming without sorting

A minimum-weight subset of prescribed cardinality is separated from its
complement by a threshold. The exchange argument handles ties and gives the
hinge duality used by both IE-21 and IE-22. Empty selections are included.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NLA.RowDeletion

lemma hinge_nonneg (t y : ℝ) : 0 ≤ hinge t y := le_max_right _ _

lemma sub_le_hinge (t y : ℝ) : t - y ≤ hinge t y := le_max_left _ _

lemma hinge_eq_zero {t y : ℝ} (h : t ≤ y) : hinge t y = 0 :=
  max_eq_right (sub_nonpos.mpr h)

lemma hinge_eq_sub {t y : ℝ} (h : y ≤ t) : hinge t y = t - y :=
  max_eq_left (sub_nonneg.mpr h)

lemma abs_hinge_sub_hinge_right (t y z : ℝ) :
    |hinge t y - hinge t z| ≤ |y - z| := by
  unfold hinge
  have h := abs_max_sub_max_le_abs (t - y) (t - z) 0
  simpa [abs_sub_comm, sub_sub_sub_cancel_left] using h

lemma abs_hinge_sub_hinge_left (t s y : ℝ) :
    |hinge t y - hinge s y| ≤ |t - s| := by
  unfold hinge
  simpa using abs_max_sub_max_le_abs (t - y) (s - y) 0

/-- Every threshold is a lower bound on every retained sum of the right size. -/
theorem finiteThreshold_le_sum {m k : ℕ} (y : Fin m → ℝ)
    (S : Finset (Fin m)) (hS : S.card = k) (t : ℝ) :
    finiteThreshold k y t ≤ ∑ i ∈ S, y i := by
  classical
  have hsub : ∑ i ∈ S, (t - y i) ≤ ∑ i ∈ S, hinge t (y i) :=
    Finset.sum_le_sum fun i _ ↦ sub_le_hinge t (y i)
  have hall : ∑ i ∈ S, hinge t (y i) ≤ ∑ i, hinge t (y i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ ↦ hinge_nonneg t (y i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hS] at hsub
  unfold finiteThreshold
  linarith

/-- Exchanging one selected index for an unselected one proves separation. -/
lemma minimizing_subset_separates {m k : ℕ} (y : Fin m → ℝ)
    {S : Finset (Fin m)} (hS : S.card = k)
    (hmin : ∀ T : Finset (Fin m), T.card = k → (∑ i ∈ S, y i) ≤ ∑ i ∈ T, y i)
    {i j : Fin m} (hi : i ∈ S) (hj : j ∉ S) : y i ≤ y j := by
  classical
  have hj' : j ∉ S.erase i := fun h ↦ hj (Finset.mem_of_mem_erase h)
  have hc : (insert j (S.erase i)).card = k := by
    rw [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hi]
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have h := hmin (insert j (S.erase i)) hc
  rw [Finset.sum_insert hj'] at h
  have he := Finset.sum_erase_add S y hi
  linarith

/-- A minimum subset admits a nonnegative threshold certificate. -/
theorem exists_trimming_certificate {m k : ℕ} (hk : k ≤ m)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∃ S : Finset (Fin m), S.card = k ∧
      ∃ t : ℝ, 0 ≤ t ∧ (∀ i ∈ S, y i ≤ t) ∧
        (∀ i ∉ S, t ≤ y i) ∧
        finiteThreshold k y t = ∑ i ∈ S, y i := by
  classical
  have hne : (Finset.univ.powersetCard k : Finset (Finset (Fin m))).Nonempty := by
    exact Finset.powersetCard_nonempty.mpr (by simpa using hk)
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image
    (Finset.univ.powersetCard k) (fun S : Finset (Fin m) ↦ ∑ i ∈ S, y i) hne
  have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
  have hmin' : ∀ T : Finset (Fin m), T.card = k → (∑ i ∈ S, y i) ≤ ∑ i ∈ T, y i :=
    fun T hT ↦ hmin T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hT⟩)
  by_cases hzero : S = ∅
  · subst S
    have hkzero : k = 0 := by simpa using hcard.symm
    subst k
    refine ⟨∅, rfl, 0, le_rfl, by simp, fun i _ ↦ hy i, ?_⟩
    simp [finiteThreshold, hinge_eq_zero (hy _)]
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image S y (Finset.nonempty_iff_ne_empty.mpr hzero)
    have hsep : ∀ j ∉ S, y i ≤ y j :=
      fun j hj ↦ minimizing_subset_separates y hcard hmin' hi hj
    refine ⟨S, hcard, y i, hy i, hmax, hsep, ?_⟩
    have hsum : (∑ j, hinge (y i) (y j)) = ∑ j ∈ S, (y i - y j) := by
      calc
        _ = ∑ j ∈ S, hinge (y i) (y j) := by
          symm
          exact Finset.sum_subset (Finset.subset_univ S)
            (fun j _ hj ↦ hinge_eq_zero (hsep j hj))
        _ = _ := Finset.sum_congr rfl fun j hj ↦ hinge_eq_sub (hmax j hj)
    unfold finiteThreshold
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    ring

/-- Exact finite trimming duality, including `k=0`, `k=m`, and tied values. -/
theorem finite_trimming_duality {m k : ℕ} (hk : k ≤ m)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    sInf {v : ℝ | ∃ S : Finset (Fin m), S.card = k ∧ v = ∑ i ∈ S, y i} =
      sSup (finiteThreshold k y '' Set.Ici 0) := by
  obtain ⟨S, hS, t, ht, _, _, heq⟩ := exists_trimming_certificate hk y hy
  have hmem : (∑ i ∈ S, y i) ∈
      {v : ℝ | ∃ S : Finset (Fin m), S.card = k ∧ v = ∑ i ∈ S, y i} :=
    ⟨S, hS, rfl⟩
  have hmin : ∀ v ∈ {v : ℝ | ∃ S : Finset (Fin m), S.card = k ∧ v = ∑ i ∈ S, y i},
      (∑ i ∈ S, y i) ≤ v := by
    rintro v ⟨T, hT, rfl⟩
    rw [← heq]
    exact finiteThreshold_le_sum y T hT t
  have hinf : sInf {v : ℝ | ∃ S : Finset (Fin m), S.card = k ∧ v = ∑ i ∈ S, y i} =
      ∑ i ∈ S, y i :=
    le_antisymm (csInf_le ⟨_, hmin⟩ hmem) (le_csInf ⟨_, hmem⟩ hmin)
  have hupper : ∀ v ∈ finiteThreshold k y '' Set.Ici 0, v ≤ ∑ i ∈ S, y i := by
    rintro v ⟨u, _, rfl⟩
    exact finiteThreshold_le_sum y S hS u
  have hvalue : (∑ i ∈ S, y i) ∈ finiteThreshold k y '' Set.Ici 0 := ⟨t, ht, heq⟩
  rw [hinf]
  exact le_antisymm (le_csSup ⟨_, hupper⟩ hvalue) (csSup_le ⟨_, hvalue⟩ hupper)

lemma finiteThreshold_le_total_sub {m k : ℕ} (y : Fin m → ℝ) (t : ℝ) :
    finiteThreshold k y t ≤ (∑ i, y i) - ((m : ℝ) - k) * t := by
  have h : (∑ i, (t - y i)) ≤ ∑ i, hinge t (y i) :=
    Finset.sum_le_sum fun i _ ↦ sub_le_hinge t (y i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  unfold finiteThreshold
  linarith

/-- Above this cutoff the dual objective is nonpositive. This avoids bounding
an order statistic or counting the observations below a threshold. -/
theorem finiteThreshold_nonpos_above {m k : ℕ} (hk : k ≤ m)
    (y : Fin m → ℝ) {L t : ℝ} (hmean : (∑ i, y i) ≤ ((m : ℝ) - k) * L)
    (ht : L ≤ t) : finiteThreshold k y t ≤ 0 := by
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hkm)
  have h := finiteThreshold_le_total_sub (k := k) y t
  linarith

/-- A bounded threshold certificate follows solely from a bound on the total sum. -/
theorem exists_bounded_trimming_certificate {m k : ℕ} (hk : k ≤ m)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) {L : ℝ} (hL : 0 ≤ L)
    (hmean : (∑ i, y i) ≤ ((m : ℝ) - k) * L) :
    ∃ S : Finset (Fin m), S.card = k ∧
      ∃ t ∈ Set.Icc 0 L, finiteThreshold k y t = ∑ i ∈ S, y i := by
  obtain ⟨S, hS, t, ht, _, _, heq⟩ := exists_trimming_certificate hk y hy
  by_cases htl : t ≤ L
  · exact ⟨S, hS, t, ⟨ht, htl⟩, heq⟩
  · have hnonpos := finiteThreshold_nonpos_above hk y hmean (le_of_not_ge htl)
    have hsum : (∑ i ∈ S, y i) = 0 :=
      le_antisymm (heq ▸ hnonpos) (Finset.sum_nonneg fun i _ ↦ hy i)
    refine ⟨S, hS, 0, ⟨le_rfl, hL⟩, ?_⟩
    simp [finiteThreshold, hinge_eq_zero (hy _), hsum]

lemma finiteThreshold_sub_bounds {m k : ℕ} (hk : k ≤ m)
    (y : Fin m → ℝ) {s t : ℝ} (hst : s ≤ t) :
    -((m : ℝ) * (t - s)) ≤ finiteThreshold k y t - finiteThreshold k y s ∧
      finiteThreshold k y t - finiteThreshold k y s ≤ (m : ℝ) * (t - s) := by
  have hlo : 0 ≤ ∑ i, (hinge t (y i) - hinge s (y i)) := by
    apply Finset.sum_nonneg
    intro i _
    exact sub_nonneg.mpr (max_le_max (sub_le_sub_right hst _) le_rfl)
  have hhi : (∑ i, (hinge t (y i) - hinge s (y i))) ≤ (m : ℝ) * (t - s) := by
    calc
      _ ≤ ∑ _i : Fin m, (t - s) := Finset.sum_le_sum fun i _ ↦
        (le_abs_self _).trans ((abs_hinge_sub_hinge_left t s (y i)).trans_eq
          (abs_of_nonneg (sub_nonneg.mpr hst)))
      _ = _ := by simp [mul_sub]
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmul := mul_le_mul_of_nonneg_right hkm (sub_nonneg.mpr hst)
  have hmul0 := mul_nonneg hk0 (sub_nonneg.mpr hst)
  simp only [Finset.sum_sub_distrib] at hlo hhi
  unfold finiteThreshold
  constructor <;> nlinarith

theorem abs_finiteThreshold_sub_le {m k : ℕ} (hk : k ≤ m)
    (y : Fin m → ℝ) (t s : ℝ) :
    |finiteThreshold k y t - finiteThreshold k y s| ≤ (m : ℝ) * |t - s| := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact abs_le.mpr (finiteThreshold_sub_bounds hk y hst)
  · rw [abs_sub_comm (finiteThreshold k y t), abs_sub_comm t,
      abs_of_nonneg (sub_nonneg.mpr hts)]
    exact abs_le.mpr (finiteThreshold_sub_bounds hk y hts)

end NLA.RowDeletion

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original MF-06 solution: George Stepaniants.

Symbolic finite-product telescoping bounds every determinant difference. The
auxiliary estimate keeps one factor L until the final positive cancellation,
so the empty finite product is handled without a predecessor-power exception.
No matrix, permutation, dimension or interval is enumerated by computation.
-/
import NLA.MF06.CompoundNorm

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF06
open NLA.MF07

lemma finite_prod_norm_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (L : ℝ) (hf : ∀ i ∈ s, ‖f i‖ ≤ L) :
    ‖∏ i ∈ s, f i‖ ≤ L ^ s.card := by
  rw [norm_prod]
  calc
    ∏ i ∈ s, ‖f i‖ ≤ ∏ _i ∈ s, L := Finset.prod_le_prod (fun i _ => norm_nonneg _) hf
    _ = L ^ s.card := Finset.prod_const L

lemma finite_prod_difference_mul_bound {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ L) (hg : ∀ i ∈ s, ‖g i‖ ≤ L)
    (hdiff : ∀ i ∈ s, ‖f i - g i‖ ≤ D) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ * L ≤ (s.card : ℝ) * L ^ s.card * D := by
  classical
  revert hf hg hdiff
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro hf hg hdiff
    have hfs := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hds := fun i hi => hdiff i (Finset.mem_insert_of_mem hi)
    have hi := ih hfs hgs hds
    have hp := finite_prod_norm_bound s g L hgs
    have hid : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
        (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hid]
    calc
      ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * ∏ i ∈ s, g i‖ * L ≤
          (‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ +
            ‖f a - g a‖ * ‖∏ i ∈ s, g i‖) * L := by
        exact mul_le_mul_of_nonneg_right (by simpa only [norm_mul] using (norm_add_le
          (f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
          ((f a - g a) * ∏ i ∈ s, g i))) hL
      _ ≤ (L * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ + D * L ^ s.card) * L := by
        apply mul_le_mul_of_nonneg_right _ hL
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hf a (Finset.mem_insert_self _ _)) (norm_nonneg _))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hp (norm_nonneg _) hD)
      _ = L * (‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ * L) + D * L ^ (s.card + 1) := by
        rw [pow_succ]
        ring
      _ ≤ L * ((s.card : ℝ) * L ^ s.card * D) + D * L ^ (s.card + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hi hL) le_rfl
      _ = ((s.card + 1 : ℕ) : ℝ) * L ^ (s.card + 1) * D := by
        push_cast
        rw [pow_succ]
        ring

lemma determinant_difference_bound {k : ℕ} (hk : 1 ≤ k) (A B : Square k)
    (L D : ℝ) (hL : 0 < L) (hD : 0 ≤ D)
    (hA : ∀ i j, ‖A i j‖ ≤ L) (hB : ∀ i j, ‖B i j‖ ≤ L)
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ D) :
    ‖Matrix.det A - Matrix.det B‖ ≤
      (Nat.factorial k : ℝ) * (k : ℝ) * L ^ (k - 1) * D := by
  have hproduct (σ : Equiv.Perm (Fin k)) :
      ‖(∏ i, A (σ i) i) - ∏ i, B (σ i) i‖ ≤ (k : ℝ) * L ^ (k - 1) * D := by
    have h := finite_prod_difference_mul_bound Finset.univ (fun i => A (σ i) i)
      (fun i => B (σ i) i) L D hL.le hD
      (fun i _ => hA _ _) (fun i _ => hB _ _) (fun i _ => hAB _ _)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    apply (mul_le_mul_iff_left₀ hL).mp
    calc
      _ ≤ (k : ℝ) * L ^ k * D := h
      _ = ((k : ℝ) * L ^ (k - 1) * D) * L := by
        have hp : L ^ k = L ^ (k - 1) * L := by
          simpa only [Nat.sub_add_cancel hk] using (pow_succ L (k - 1))
        rw [hp]
        ring
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  calc
    ‖∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ • ∏ i, A (σ i) i) - (Equiv.Perm.sign σ • ∏ i, B (σ i) i))‖ ≤
        ∑ σ : Equiv.Perm (Fin k),
          ‖(Equiv.Perm.sign σ • ∏ i, A (σ i) i) - (Equiv.Perm.sign σ • ∏ i, B (σ i) i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), (k : ℝ) * L ^ (k - 1) * D := by
      apply Finset.sum_le_sum
      intro σ _
      rw [← smul_sub, norm_units_zsmul]
      exact hproduct σ
    _ = (Nat.factorial k : ℝ) * (k : ℝ) * L ^ (k - 1) * D := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]
      ring

theorem compound_local_lipschitz {d : ℕ} (k : ℕ) (hk0 : 1 ≤ k) (hkd : k ≤ d)
    (L : ℝ) (hL : 0 < L) (A B : Square d)
    (hA : spectralNorm A ≤ L) (hB : spectralNorm B ≤ L) :
    0 < compoundLipschitzConstant d k L ∧
    spectralNorm (compoundMatrix k A - compoundMatrix k B) ≤
      compoundLipschitzConstant d k L * spectralNorm (A - B) := by
  have hdim : 0 < (compoundDim d k : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le ((compound_dimensions d k).2 hkd))
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hk0)
  have hfac : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hc : 0 < compoundLipschitzConstant d k L := by
    unfold compoundLipschitzConstant
    positivity
  refine ⟨hc, ?_⟩
  have hentry (i j : Fin (compoundDim d k)) :
      ‖(compoundMatrix k A - compoundMatrix k B) i j‖ ≤
        (Nat.factorial k : ℝ) * (k : ℝ) * L ^ (k - 1) * spectralNorm (A - B) :=
    determinant_difference_bound hk0
      (A.submatrix (minorCoordinate d k i) (minorCoordinate d k j))
      (B.submatrix (minorCoordinate d k i) (minorCoordinate d k j))
      L (spectralNorm (A - B)) hL (spectralNorm_nonneg _)
      (fun u v => (spectralNorm_entry_bound A _ _).trans hA)
      (fun u v => (spectralNorm_entry_bound B _ _).trans hB)
      (fun u v => spectralNorm_entry_bound (A - B) _ _)
  calc
    spectralNorm (compoundMatrix k A - compoundMatrix k B) ≤
        (compoundDim d k : ℝ) *
          ((Nat.factorial k : ℝ) * (k : ℝ) * L ^ (k - 1) * spectralNorm (A - B)) :=
      spectralNorm_le_card_mul_entry_bound _ _
        (mul_nonneg (mul_nonneg (mul_nonneg hfac.le hkR.le) (pow_nonneg hL.le _))
          (spectralNorm_nonneg _)) hentry
    _ = compoundLipschitzConstant d k L * spectralNorm (A - B) := by
      unfold compoundLipschitzConstant
      ring

#print axioms compound_local_lipschitz
#assert_trust kernel compound_local_lipschitz

end NLA.MF06
